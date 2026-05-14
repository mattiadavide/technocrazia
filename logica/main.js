import { SWARM_SIZE, STRIDE, IDX_X, IDX_Y, IDX_TX, IDX_TY, IDX_OPACITY, IDX_T_OPACITY, IDX_ACTIVE, IDX_PRIO, IDX_REACT, IDX_SCALE, IDX_Z, PHI } from './swarm_core.js';

const MAX_PARTICLES = SWARM_SIZE;
let swarmWorkerInstance = null;

const swarmSAB = new SharedArrayBuffer(MAX_PARTICLES * STRIDE * 4);
const glyphSAB = new SharedArrayBuffer(MAX_PARTICLES * 2);
const syncSAB = new SharedArrayBuffer(4);

let currentSwarmData = new Float32Array(swarmSAB);
let currentGlyphIDs = new Uint16Array(glyphSAB);
let syncArray = new Int32Array(syncSAB);

let atlasCanvas = null;
let atlasLookup = [];
const atlasFastMap = new Uint16Array(65536);
let dotGlyphID = 0;

function initGlyphAtlas() {
    const seedPx = 25;
    // Aggiungi il simbolo '●' alla fine dell'alfabeto
    const ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789@#%&*+=-_<>{}[] .:-*+ ●"; 
    const chars = ALPHABET.split("");
    const size = Math.ceil(seedPx * 2.0);

    atlasCanvas = document.createElement('canvas');
    const ctx = atlasCanvas.getContext('2d');
    ctx.imageSmoothingEnabled = false;

    const cols = 16;
    atlasCanvas.width = cols * size;
    atlasCanvas.height = Math.ceil(chars.length / cols) * size;
    ctx.textBaseline = 'middle';
    ctx.textAlign = 'center';

    let count = 0;
    chars.forEach(char => {
        const u = (count % cols) * size;
        const v = Math.floor(count / cols) * size;
        ctx.fillStyle = '#ffffff';
        if (char === ' ') {
            ctx.fillRect(u + size * 0.05, v + size * 0.05, size * 0.9, size * 0.9);
        } else if (char === '●') {
            // DISEGNAMO UN CERCHIO PERFETTO PER LA FUSIONE
            ctx.beginPath();
            ctx.arc(u + size / 2, v + size / 2, size * 0.45, 0, Math.PI * 2);
            ctx.fill();
        } else {
            ctx.font = `bold ${Math.floor(size * 0.9)}px 'Courier New', Courier, monospace`;
            ctx.fillText(char, u + (size / 2), v + (size / 2));
        }
        atlasFastMap[char.charCodeAt(0)] = count;
        atlasLookup[count] = [u, v, size, size];
        count++;
    });

    dotGlyphID = atlasFastMap['+'.charCodeAt(0)] || 0;
}

let logoTargets = [];
// FIX #9: basePixels come 4 TypedArray piatti — zero object heap, cache-friendly
let bpX    = null;  // Float32Array
let bpY    = null;  // Float32Array
let bpNY   = null;  // Float32Array (y normalizzata 0-1)
let bpChar = null;  // Uint32Array  (char code)
let bpCount = 0;    // numero di pixel validi
let activeParticles = 0;
let structuralLibrary = "█▓▒#H80X".split("").map(c => c.charCodeAt(0));
let fillLibrary = ".:-+*░".split("").map(c => c.charCodeAt(0));
let glyphLibrary = structuralLibrary; // Fallback

function loadAndParseLogoImage(callback) {
    const img = new Image();
    img.src = 'logo.png';
    img.onload = () => {
        const tw = 1200;
        const th = 1200;
        const memCanvas = document.createElement('canvas');
        memCanvas.width = tw;
        memCanvas.height = th;
        const ctx = memCanvas.getContext('2d', { willReadFrequently: true });
        ctx.fillStyle = 'black';
        ctx.fillRect(0, 0, tw, th);

        const ratio = img.width / img.height;
        let drawW = 1000;
        let drawH = drawW / ratio;
        if (drawH > 1000) {
            drawH = 1000;
            drawW = drawH * ratio;
        }
        const offsetX = (tw - drawW) / 2;
        const offsetY = (th - drawH) / 2;
        ctx.drawImage(img, offsetX, offsetY, drawW, drawH);

        const imgData = ctx.getImageData(0, 0, tw, th).data;
        // FIX #9: pre-alloca il massimo possibile (tw*th), poi tronca con bpCount
        const maxPx = tw * th;
        bpX    = new Float32Array(maxPx);
        bpY    = new Float32Array(maxPx);
        bpNY   = new Float32Array(maxPx);
        bpChar = new Uint32Array(maxPx);
        bpCount = 0;
        const step = 1;

        for (let y = 0; y < th; y += step) {
            for (let x = 0; x < tw; x += step) {
                const pi = (y * tw + x) * 4;
                const brightness = (imgData[pi] + imgData[pi + 1] + imgData[pi + 2]) / 3;
                if (brightness > 128) {
                    bpX[bpCount]    = x;
                    bpY[bpCount]    = y;
                    bpNY[bpCount]   = y / th;
                    bpChar[bpCount] = glyphLibrary[bpCount % glyphLibrary.length];
                    bpCount++;
                }
            }
        }

        if (bpCount === 0) {
            console.warn("Logo has no bright pixels? Check the image.");
        }
        buildTargets();
        callback();
    };
    img.onerror = () => {
        alert("Attenzione: Impossibile trovare 'logo.png'.");
        buildTargets();
        callback();
    };
}

function buildTargets() {
    logoTargets = [];
    if (bpCount === 0) return;

    activeParticles = MAX_PARTICLES;

    const winW = 1920;
    const winH = 1080;
    const scaleArea = Math.min(winW, winH) * 0.85 / 1200;

    // FIX #1 (invariato): costanti fuori dal loop
    const coreParticles = Math.min(activeParticles, bpCount);
    const stepSub = bpCount / coreParticles;

    // FIX #6: hash deterministico — elimina Math.random() da 60K iterazioni
    // Produco una sequenza pseudo-casuale stabile usando la sezione aurea
    const PHI_HASH = 2654435769; // Fibonacci hashing (Knuth) su Uint32

    for (let i = 0; i < activeParticles; i++) {
        let bpi;

        if (i < coreParticles) {
            bpi = Math.floor(i * stepSub);
        } else {
            // FIX #6: hash deterministico al posto di Math.random()
            bpi = ((i * PHI_HASH) >>> 0) % bpCount;
        }

        // Clamp di sicurezza
        if (bpi >= bpCount) bpi = 0;

        logoTargets.push({
            x: (winW / 2) + (bpX[bpi] - 600) * scaleArea,
            y: (winH / 2) + (bpY[bpi] - 600) * scaleArea,
            ny: bpNY[bpi],
            originalChar: bpChar[bpi],
            isCoreLogo: i < coreParticles
        });
    }
}

// ================= TECHNO GEOMETRY LIBRARY ================= //
const geomOut = { x: 0, y: 0, depth: 1.0, isSilhouette: false, nx: 0, ny: 0, nz: 0 };

// 1. STATO FISICO A BLOCCHI (Cartesiano e Rigido)
const NUM_BLOCKS = 32;
const blockRotZ = new Float32Array(NUM_BLOCKS);
const blockRotX = new Float32Array(NUM_BLOCKS);
const blockRotY = new Float32Array(NUM_BLOCKS);
const blockExtrusion = new Float32Array(NUM_BLOCKS);

// --- VARIABILI CRISTALLO ---
let crystalState = 0;
let latticeX = 1.0, latticeY = 1.0, latticeZ = 1.0;
let lastKickBin = 0, lastSnareBin = 0;
let lastMutationTime = 0, lastSnareTime = 0;

// ================= GEOMETRIA AVANZATA BISMUTH HOPPER =================

// BUG FIX #3: Funzione estratta — aggiorna le estrusioni dei blocchi UNA volta per frame
// (prima era dentro getGantzGrafTarget con guard i===0, causando 3.6M typeof check/sec)
const DT_60FPS = 0.016;
function updateBlockExtrusions() {
    for (let b = 0; b < NUM_BLOCKS; b++) {
        const arr = (b % 2 === 0 && dataArrayL) ? dataArrayL :
            (dataArrayR) ? dataArrayR : dataArray;
        const signal = (arr[Math.floor(b / 2) % 50] || 0) / 255.0;
        const shock = signal * signal * signal;
        const targetExtrusion = shock * 1200.0;
        if (targetExtrusion > blockExtrusion[b]) {
            blockExtrusion[b] += (targetExtrusion - blockExtrusion[b]) * (DT_60FPS * 85.0);
        } else {
            blockExtrusion[b] += (targetExtrusion - blockExtrusion[b]) * (DT_60FPS * 25.0);
        }
    }
}

function getGantzGrafTarget(i, numParticles, time, winW, winH, rms, audioValue, rmsL = 0, rmsR = 0) {
    // BUG FIX #3: updateBlockExtrusions() è ora chiamata una volta/frame in sysLoop, non qui.

    const ptsPerBlock = numParticles / NUM_BLOCKS;
    const blockId = Math.floor(i / ptsPerBlock) || 0;
    const localI = i % ptsPerBlock;
    const t = localI / ptsPerBlock;

    // BUG FIX #8: PHI_LOCAL → PHI (costante di modulo, evita ridichiarazioni ×60K)
    const rand1 = (i * PHI) % 1.0;

    // --- PARAMETRI BASE CRISTALLO (Audio-Driven) ---
    // VOLUME TOTALE → Scala globale (il solido respira con l'RMS totale)
    const volumePulse = 1.0 + (rms * 1.5);
    const baseScale = winH * 0.35 * volumePulse;
    const layerIdx = Math.floor(blockId / 4);
    const stepSize = baseScale * 0.06;
    const size = baseScale * (1.0 - (layerIdx * 0.05));
    const zBase = (layerIdx * stepSize * 1.5);

    // TREBLE → Estrusione (suoni brillanti = cristallo alto e spigoloso)
    const freqOffset = (layerIdx * 4) % 128;
    const rawColAudio = (typeof dataArray !== "undefined") ? (dataArray[freqOffset] / 255.0) : 0;
    const colAudio = rawColAudio > 0.2 ? rawColAudio : 0;
    const trebleBoost = 0.6 + audioTreble * 2.0;
    const totalExtrusion = colAudio * baseScale * trebleBoost;

    // MIDS + CENTROID → Numero di lati (complessità polimorfica)
    // Centroide basso (suoni scuri) = pochi lati (triangoli, quadrati)
    // Centroide alto (suoni brillanti) = molti lati (esagoni, quasi cerchi)
    const sidesCount = 3 + Math.floor(audioSpectralCentroid * 5);

    // --- ARCHITETTURA CINETICA (DENSITA' 60K) ---
    const tGrid = (i % ptsPerBlock) / ptsPerBlock;

    let isSilhouette = false;
    let x = 0, y = 0, z = zBase;
    let nx = 0, ny = 0, nz = 1;
    let layerType = "mesh";

    if (tGrid < 0.25) {
        // --- 25% ANELLI SPETTRALI (8 strati, 64 snap) ---
        layerType = "structural";
        const ringT = tGrid / 0.25;
        const ringIdx = Math.floor(ringT * 8);
        const localT = (ringT * 8) % 1.0;
        const snappedT = Math.floor(localT * 64) / 64;

        const side = Math.floor(snappedT * sidesCount);
        const st = (snappedT * sidesCount) % 1.0;
        const angleStep = (Math.PI * 2) / sidesCount;
        const startA = side * angleStep, endA = (side + 1) * angleStep;

        const freqBin = Math.floor(snappedT * 128);
        const isLeft = Math.cos(startA) < 0;
        const arr = (isLeft && typeof dataArrayL !== "undefined" && dataArrayL) ? dataArrayL :
            (!isLeft && typeof dataArrayR !== "undefined" && dataArrayR) ? dataArrayR : dataArray;
        const ripple = (typeof arr !== "undefined" && arr) ? (arr[freqBin % 128] / 255.0) * 45.0 : 0;
        const rSize = size + ripple;

        x = Math.cos(startA) * rSize + (Math.cos(endA) * rSize - Math.cos(startA) * rSize) * st;
        y = Math.sin(startA) * rSize + (Math.sin(endA) * rSize - Math.sin(startA) * rSize) * st;
        z = zBase + (ringIdx / 7.0) * totalExtrusion;

        const normA = side * angleStep + angleStep * 0.5;
        nx = Math.cos(normA); ny = Math.sin(normA); nz = 0;
        isSilhouette = true;
    } else if (tGrid < 0.35) {
        // --- 10% PILASTRI KINETICI ---
        layerType = "structural";
        const pillarT = (tGrid - 0.25) / 0.10;
        const cornerIdx = Math.floor(pillarT * sidesCount);
        const localPillarT = (pillarT * sidesCount) % 1.0;
        const angle = cornerIdx * ((Math.PI * 2) / sidesCount);
        const isLeft = Math.cos(angle) < 0;
        const localRms = isLeft ? rmsL : rmsR;
        const bend = Math.sin(localPillarT * Math.PI) * (localRms * 160.0);

        x = Math.cos(angle) * (size + bend);
        y = Math.sin(angle) * (size + bend);
        z = zBase + localPillarT * totalExtrusion;

        nx = Math.cos(angle); ny = Math.sin(angle); nz = 0;
        isSilhouette = true;
    } else if (tGrid < 0.85) {
        // --- 50% SOLID VOLUME (Massa Bismuth) ---
        layerType = "mesh";
        // Hash spaziale deterministico (ZERO flickering)
        const phi_h = (i * PHI) % 1.0;
        const theta_h = (i * PHI * PHI) % 1.0;
        const angle = theta_h * Math.PI * 2;

        // Raggio confinato al poligono (non circolare)
        const angleStep = (Math.PI * 2) / sidesCount;
        const sectorLocal = ((angle % angleStep) + angleStep) % angleStep;
        const halfStep = angleStep * 0.5;
        const polyEdge = size * Math.cos(halfStep) / Math.cos(Math.abs(sectorLocal - halfStep));

        // Audio-reactive: il volume pulsa con L/R
        const isLeft = Math.cos(angle) < 0;
        const localRms = isLeft ? rmsL : rmsR;
        const audioExpand = 1.0 + localRms * 0.4;

        // sqrt(hash) = distribuzione uniforme nell'area poligonale
        const r = Math.sqrt(phi_h) * polyEdge * audioExpand;

        x = Math.cos(angle) * r;
        y = Math.sin(angle) * r;
        
        // 1. GANTZ GRAF: piastre di metallo solido
        const numPlates = 6;
        const plateZ = Math.floor(((i * PHI * 0.618) % 1.0) * numPlates) / (numPlates - 1);
        z = zBase + plateZ * totalExtrusion;
        
        // 2. GANTZ GRAF FLAT SHADING: Normali perpendicolari alla faccia per un look meccanico e spigoloso
        const faceNormalAngle = Math.floor(angle / angleStep) * angleStep + halfStep;
        nx = Math.cos(faceNormalAngle); 
        ny = Math.sin(faceNormalAngle); 
        nz = 0; 
        
        isSilhouette = false;
    } else {
        // --- 15% CORE (Nucleo Doppia Elica) ---
        layerType = "structural";
        const coreT = (tGrid - 0.85) / 0.15;
        const helixAngle = coreT * Math.PI * 6;
        const helixR = size * (0.15 + coreT * 0.15);
        x = Math.cos(helixAngle) * helixR;
        y = Math.sin(helixAngle) * helixR;
        z = zBase + coreT * totalExtrusion;
        nx = 0; ny = 0; nz = 1;
        isSilhouette = true;
    }

    geomOut.isSilhouette = isSilhouette;
    geomOut.layerType = layerType;

    // --- DEFORMAZIONI GLOBALI ---
    // STEREO WIDTH → Twist (differenza L-R torce il cristallo)
    const twistAngle = z * (0.0003 + audioStereoWidth * 0.003) * (rms * 2.0);
    const cosTwist = Math.cos(twistAngle), sinTwist = Math.sin(twistAngle);
    const txG = x * cosTwist - y * sinTwist;
    const tyG = x * sinTwist + y * cosTwist;
    x = txG; y = tyG;

    // Taper bilanciato
    const taper = 1.0 - (z / (baseScale * 5.0)) * 0.3;
    x *= taper; y *= taper;

    // --- PERMUTAZIONE E ROTAZIONE FINALE ---
    let px = x, py = y, pz = z;
    if (crystalState === 1) { px = y; py = z; pz = x; }
    else if (crystalState === 2) { px = z; py = -x; pz = y; }
    else if (crystalState === 3) { px = -y; py = x; pz = -z; }

    x = px * latticeX;
    y = py * latticeY;
    z = pz * latticeZ;

    // Rotazione asincrona molto più lenta e controllata
    const isBlockLeft = (blockId % 2 === 0);
    const bArr = (isBlockLeft && typeof dataArrayL !== "undefined" && dataArrayL) ? dataArrayL :
        (!isBlockLeft && typeof dataArrayR !== "undefined" && dataArrayR) ? dataArrayR : dataArray;
    const rawBlockAudio = (typeof bArr !== "undefined" && bArr) ? (bArr[layerIdx % 64] / 255.0) : 0;
    const blockAudio = rawBlockAudio > 0.3 ? (rawBlockAudio - 0.3) : 0;
    let rawRZ = isNaN(blockRotZ[blockId]) ? 0 : blockRotZ[blockId];
    rawRZ += blockAudio * Math.PI * 0.2;
    rawRZ = Math.round(rawRZ / (Math.PI / 2)) * (Math.PI / 2); // Snap più rigido
    let cZ = Math.cos(rawRZ), sZ = Math.sin(rawRZ);
    let lx = x * cZ - y * sZ;
    let ly = x * sZ + y * cZ;
    let lz = z;
    // Ruotiamo anche la normale
    let lnx = nx * cZ - ny * sZ;
    let lny = nx * sZ + ny * cZ;
    let lnz = nz;

    let rawRX = isNaN(blockRotX[blockId]) ? 0 : blockRotX[blockId];
    rawRX = Math.round(rawRX / (Math.PI / 2)) * (Math.PI / 2);
    let cX = Math.cos(rawRX), sX = Math.sin(rawRX);
    let ly2 = ly * cX - lz * sX;
    let lz2 = ly * sX + lz * cX;
    // Ruotiamo normale su X
    let lny2 = lny * cX - lnz * sX;
    let lnz2 = lny * sX + lnz * cX;

    let rawRY = isNaN(blockRotY[blockId]) ? 0 : blockRotY[blockId];
    rawRY = Math.round(rawRY / (Math.PI / 2)) * (Math.PI / 2);
    let cY = Math.cos(rawRY), sY = Math.sin(rawRY);
    let lx2 = lx * cY + lz2 * sY;
    let lz3 = -lx * sY + lz2 * cY;
    // Ruotiamo normale su Y
    let lnx2 = lnx * cY + lnz2 * sY;
    let lnz3 = -lnx * sY + lnz2 * cY;

    x = lx2; y = ly2; z = lz3;
    nx = lnx2; ny = lny2; nz = lnz3;

    // --- ROTAZIONE GLOBALE (Frame Cache — zero trig ridondante) ---
    let rx = x * fGcZ - y * fGsZ;
    let ry = x * fGsZ + y * fGcZ;
    let rz = z;
    let rnx = nx * fGcZ - ny * fGsZ;
    let rny = nx * fGsZ + ny * fGcZ;
    let rnz = nz;

    let gx = rx * fGcY + rz * fGsY;
    let gz = -rx * fGsY + rz * fGcY;
    let gnx = rnx * fGcY + rnz * fGsY;
    let gnz = -rnx * fGsY + rnz * fGcY;

    let gy = ry * fGcX - gz * fGsX;
    let gz2 = ry * fGsX + gz * fGcX;
    let gny = rny * fGcX - gnz * fGsX;
    let gnz2 = rny * fGsX + gnz * fGcX;

    geomOut.nx = gnx; geomOut.ny = gny; geomOut.nz = gnz2;

    gx *= fPump; gy *= fPump; gz2 *= fPump;

    const perspective = 1200.0 / Math.max(10, (1200.0 - gz2 + (fCamZ - 1200)));

    geomOut.x = (960 + gx * perspective) || 960;
    geomOut.y = (540 + gy * perspective) || 540;
    geomOut.depth = perspective || 1.0;

    return geomOut;
}

const geometries = [getGantzGrafTarget];
let currentGeometryIdx = 0;
let targetGeometryIdx = 0;
let geometryMorph = 1.0;
let beatCount = 0;
let lastBeatTime = 0;

// --- FISICA PLANETARIA E CINEMATOGRAFIA ---
let autoRotationX = 0;
let autoRotationY = 0;
let autoRotationZ = 0;
const EARTH_ANGULAR_VELOCITY = 0.0000727; // Velocità reale in rad/s
const TIME_SCALE = 2000; // Accelera il tempo per rendere la rotazione visibile

let cameraCutOffsetX = 0;
let cameraCutOffsetY = 0;
let cameraCutOffsetZ = 0;
let lastCameraCutTime = 0;

// --- CONTROLLI ORBITALI MOUSE ---
let mouseX = 0, mouseY = 0;
let targetOrbitX = 0, targetOrbitY = 0;
let currentOrbitX = 0, currentOrbitY = 0;
let baseZoom = 2800, autoZoom = 0, targetZoom = 2800, mouseZoom = 2800;
let isMouseDown = false;
let userGlyphScale = 1.5;

// Frame rotation cache (computed once per frame, consumed by all 60K particles)
let fGcZ = 1, fGsZ = 0, fGcY = 1, fGsY = 0, fGcX = 1, fGsX = 0;
let fPump = 1, fCamZ = 1200;

// Audio Feature Extraction (computed once per frame, drives geometry)
let audioBass = 0, audioMid = 0, audioTreble = 0;
let audioSpectralCentroid = 0.5;
let audioStereoWidth = 0;
let kickPulse = 0; // Decaying radial pulse on kick transients

const sliderZoom = document.getElementById('slider-zoom');
const sliderScale = document.getElementById('slider-scale');
const sliderOrbitX = document.getElementById('slider-orbit-x');
const sliderOrbitY = document.getElementById('slider-orbit-y');

sliderZoom.addEventListener('input', (e) => { targetZoom = parseFloat(e.target.value); baseZoom = targetZoom; autoZoom = 0; });
sliderScale.addEventListener('input', (e) => { userGlyphScale = parseFloat(e.target.value); });
sliderOrbitX.addEventListener('input', (e) => { targetOrbitX = parseFloat(e.target.value); });
sliderOrbitY.addEventListener('input', (e) => { targetOrbitY = parseFloat(e.target.value); });

window.addEventListener("mousedown", (e) => { if (e.button === 0) isMouseDown = true; });
window.addEventListener("mouseup", () => { isMouseDown = false; });
window.addEventListener("mousemove", (e) => {
    if (!isMouseDown) return;
    if (e.target.tagName === 'INPUT' || e.target.closest('#control-panel')) return;
    targetOrbitY = ((e.clientX / window.innerWidth) * 2 - 1) * Math.PI;
    targetOrbitX = ((e.clientY / window.innerHeight) * 2 - 1) * Math.PI;
    sliderOrbitX.value = targetOrbitX;
    sliderOrbitY.value = targetOrbitY;
});
window.addEventListener("wheel", (e) => {
    if (e.target.tagName === 'INPUT' || e.target.closest('#control-panel')) return;
    e.preventDefault();
    const isPinch = e.ctrlKey;
    const delta = e.deltaY;

    if (isMouseDown || isPinch) {
        userGlyphScale = Math.max(0.2, Math.min(6.0, userGlyphScale - delta * 0.005));
        sliderScale.value = userGlyphScale;
    } else {
        baseZoom = Math.max(-2000, Math.min(4000, baseZoom + delta * 1.5));
        targetZoom = baseZoom;
        sliderZoom.value = targetZoom;
    }
}, { passive: false });

// ================= AUDIO ENGINE ================= //
let audioCtx = null;
let analyser = null;
let analyserL = null;
let analyserR = null;
let dataArray = null;
let dataArrayL = null;
let dataArrayR = null;

// ================= SPECTRAL CALIBRATION (Hz → Bin) ================= //
// Calcolati dinamicamente da audioCtx.sampleRate dopo init.
// NON usare mai bin hardcoded: il sample rate reale (44100 vs 48000) sposta
// ogni bin di ~2Hz, distorcendo kick, snare e hi-hat detection.
let SPEC = {
    binHz:        23.4,   // Hz per bin (placeholder, sovrascritto da calibrateSpectrum)
    // BANDE (indici bin calcolati da Hz reali)
    subLo:        1,      // SUB: 20 Hz
    subHi:        2,      // SUB: 40 Hz
    kickLo:       3,      // KICK: 60 Hz
    kickHi:       5,      // KICK: 120 Hz
    kickFluxLo:   3,      // Spectral Flux kick
    kickFluxHi:   5,
    lowMidLo:     7,      // LOW MID: 150 Hz
    lowMidHi:     14,     // LOW MID: 300 Hz
    snareLo:      90,     // SNARE: 2000 Hz
    snareHi:      200,    // SNARE: 4500 Hz
    snareFluxLo:  90,     // Spectral Flux snare
    snareFluxHi:  200,
    hiHatLo:      370,    // HI-HAT: 8000 Hz
    hiHatHi:      550,    // HI-HAT: 12000 Hz
    hiHatGlitch:  400,    // Hi-hat glitch probe (singolo bin)
    kickInstLo:   3,      // Kick istantaneo per shading
    kickInstHi:   5,
    kickInstN:    3,      // numero di bin nel range kick istantaneo
    snareN:       111,    // numero di bin nel range snare (per normalizzazione flux)
    kickFluxN:    3,      // numero di bin nel range kick flux
};

function calibrateSpectrum() {
    if (!audioCtx || !analyser) return;
    const nyquist  = audioCtx.sampleRate / 2;          // es. 22050 o 24000
    const nBins    = analyser.frequencyBinCount;        // fftSize / 2
    const binHz    = nyquist / nBins;                   // Hz per ogni bin
    const BIN = hz => Math.max(0, Math.min(nBins - 1, Math.round(hz / binHz)));

    SPEC.binHz       = binHz;
    SPEC.subLo       = BIN(20);
    SPEC.subHi       = BIN(40);
    SPEC.kickLo      = BIN(60);
    SPEC.kickHi      = BIN(120);
    SPEC.kickFluxLo  = BIN(60);
    SPEC.kickFluxHi  = BIN(120);
    SPEC.lowMidLo    = BIN(150);
    SPEC.lowMidHi    = BIN(300);
    SPEC.snareLo     = BIN(2000);
    SPEC.snareHi     = BIN(4500);
    SPEC.snareFluxLo = BIN(2000);
    SPEC.snareFluxHi = BIN(4500);
    SPEC.hiHatLo     = BIN(8000);
    SPEC.hiHatHi     = BIN(12000);
    SPEC.hiHatGlitch = BIN(9000);  // bin singolo per micro-glitch hi-hat
    SPEC.kickInstLo  = BIN(60);
    SPEC.kickInstHi  = BIN(120);
    SPEC.kickInstN   = Math.max(1, SPEC.kickInstHi - SPEC.kickInstLo + 1);
    SPEC.snareN      = Math.max(1, SPEC.snareHi    - SPEC.snareLo    + 1);
    SPEC.kickFluxN   = Math.max(1, SPEC.kickFluxHi - SPEC.kickFluxLo + 1);

    console.log(
        `[SPEC] sampleRate=${audioCtx.sampleRate}Hz | binHz=${binHz.toFixed(2)} | ` +
        `KICK=[${SPEC.kickLo}–${SPEC.kickHi}] SNARE=[${SPEC.snareLo}–${SPEC.snareHi}] ` +
        `HI-HAT=[${SPEC.hiHatLo}–${SPEC.hiHatHi}]`
    );
}

async function populateAudioDevices() {
    const select = document.getElementById('audio-input-select');
    try {
        if (navigator.mediaDevices && navigator.mediaDevices.getUserMedia) {
            await navigator.mediaDevices.getUserMedia({ audio: true });
        }
        const devices = await navigator.mediaDevices.enumerateDevices();
        const audioInputs = devices.filter(d => d.kind === 'audioinput');

        if (audioInputs.length > 0) {
            select.innerHTML = '<option value="system">[ SYSTEM AUDIO / LOOPBACK ]</option>';
            const defaultOpt = document.createElement('option');
            defaultOpt.value = 'default';
            defaultOpt.text = '[ DEFAULT MICROPHONE ]';
            select.appendChild(defaultOpt);

            audioInputs.forEach((device, index) => {
                if (device.deviceId === 'default' || device.deviceId === 'communications') return;
                const opt = document.createElement('option');
                opt.value = device.deviceId;
                opt.text = device.label || `[ AUDIO INPUT ${index + 1} ]`;
                select.appendChild(opt);
            });
        }
    } catch (e) {
        console.warn("Could not populate detailed devices: ", e);
    }
}
populateAudioDevices();

async function startAudio() {
    const sourceId = document.getElementById('audio-input-select').value;
    try {
        let stream;
        if (sourceId === 'system') {
            stream = await navigator.mediaDevices.getDisplayMedia({ audio: true, video: true });
        } else if (sourceId === 'default') {
            stream = await navigator.mediaDevices.getUserMedia({ audio: true });
        } else {
            stream = await navigator.mediaDevices.getUserMedia({ audio: { deviceId: { exact: sourceId } } });
        }

        audioCtx = new (window.AudioContext || window.webkitAudioContext)({ latencyHint: 'interactive' });

        analyser = audioCtx.createAnalyser();
        analyser.fftSize = 2048; // Elevata risoluzione FFT
        analyser.smoothingTimeConstant = 0.1; // Azzerata la latenza: audio in TEMPO REALE

        // Calibrazione spettrale: calcola i bin reali da Hz dopo init AudioContext
        calibrateSpectrum();

        const audioTracks = stream.getAudioTracks();
        if (audioTracks.length === 0) throw new Error("No audio track.");

        const audioStream = new MediaStream(audioTracks);
        const source = audioCtx.createMediaStreamSource(audioStream);

        // Connessione Mono globale
        source.connect(analyser);
        dataArray = new Float32Array(analyser.frequencyBinCount);

        // Setup Splitter Stereo
        const splitter = audioCtx.createChannelSplitter(2);
        source.connect(splitter);

        analyserL = audioCtx.createAnalyser();
        analyserL.fftSize = 2048;
        analyserL.smoothingTimeConstant = 0.1;
        splitter.connect(analyserL, 0);
        dataArrayL = new Float32Array(analyserL.frequencyBinCount);

        analyserR = audioCtx.createAnalyser();
        analyserR.fftSize = 2048;
        analyserR.smoothingTimeConstant = 0.1;
        splitter.connect(analyserR, 1);
        dataArrayR = new Float32Array(analyserR.frequencyBinCount);

        document.getElementById('start-btn').style.display = 'none';
        document.getElementById('params-group').style.display = 'flex';

        startRenderLoop();
    } catch (e) {
        alert("Audio Access Error: " + e.message);
    }
}

// ================= RENDER LOOP ================= //
let smoothedMorph = 0.0;
let lastTime = 0;
let beatHistory = 0.0;
let dominantHue = 0; // Colore dominante dell'intero cristallo
let kickHistory = 0.0;
let snareHistory = 0.0;

// Variabili Spectral Flux e Glitch
let prevDataArray = null;
let kickFlux = 0;
let snareFlux = 0;
let invertFrames = 0;
let gridSnapFrames = 0;

let renderLoopStarted = false;
let loopWorker = null;
function startRenderLoop() {
    if (renderLoopStarted) return;
    renderLoopStarted = true;

    const canvas = document.getElementById('swarm-matrix');
    initGlyphAtlas();

    const previewContainer = document.getElementById('preview-container');
    // Fissiamo la risoluzione interna a 1080p per prestazioni VJ zero-lag
    canvas.width = 1920;
    canvas.height = 1080;

    swarmWorkerInstance = new Worker(new URL('./swarm.worker.js', import.meta.url), { type: 'module' });

    const offscreen = canvas.transferControlToOffscreen();
    createImageBitmap(atlasCanvas).then(bitmap => {
        swarmWorkerInstance.postMessage({
            type: 'INIT',
            data: {
                canvas: offscreen,
                atlasBitmap: bitmap,
                atlasLookup,
                dpr: 1,
                dotGlyphID: dotGlyphID,
                swarmBuffer: swarmSAB,
                glyphBuffer: glyphSAB,
                syncBuffer: syncSAB
            }
        }, [offscreen, bitmap]);

        loadAndParseLogoImage(() => {
            lastTime = performance.now();
            const blob = new Blob([`
                let interval;
                self.onmessage = function(e) {
                    if (e.data === 'start') {
                        interval = setInterval(() => self.postMessage('tick'), 16);
                    } else if (e.data === 'stop') {
                        clearInterval(interval);
                    }
                };
            `], { type: 'application/javascript' });
            loopWorker = new Worker(URL.createObjectURL(blob));
            loopWorker.onmessage = () => {
                sysLoop(performance.now());
            };
            loopWorker.postMessage('start');
        });
    });

    // Nessun ResizeObserver: il canvas è fissato a 1920x1080 e usa object-fit: cover via CSS.


    // Integrazione nel Render Loop (Sintesi dei due mondi)
    function updateAudioLogic(dataArray, now, dt, rms) {
        // ALGORITMO TRANSIENTI (Spectral Flux):
        // Invece di guardare il volume continuo, valutiamo l'energia dinamica pura (Accelerazione del suono).
        
        // La storia diventa una soglia adattiva del rumore di fondo dei transienti
        kickHistory = kickHistory * 0.85 + kickFlux * 0.15;
        snareHistory = snareHistory * 0.85 + snareFlux * 0.15;

        // Un transiente avviene se il flusso istantaneo supera la media recente ed ha un impatto fisico reale
        const isPercussiveKick = (kickFlux > kickHistory * 2.5 && kickFlux > 8.0);
        const isPercussiveSnare = (snareFlux > snareHistory * 2.0 && snareFlux > 5.0);

        // MUTAZIONE RADICALE (Cambio di topologia): Avviene SOLO sui transienti percussivi
        if ((isPercussiveKick || isPercussiveSnare) && (now - lastMutationTime) > 150) {
            if (isPercussiveSnare) invertFrames = 3; // Stroboscopia Architetturale (Negative Space)
            
            lastMutationTime = now;
            crystalState = (crystalState + 1) % 4;
            for (let b = 0; b < NUM_BLOCKS; b++) {
                blockRotZ[b] += (Math.random() > 0.5 ? 1 : -1) * (Math.PI / 2);
                if (Math.random() > 0.6) blockRotX[b] += (Math.PI / 2);
                if (Math.random() > 0.8) blockRotY[b] += (Math.PI / 2);
            }
        }

        // DEFORMAZIONE FLUIDA (Elasticità):
        // I bassi dilatano l'asse X, gli acuti dilatano l'asse Y
        const targetLatticeX = 1.0 + (audioBass * 2.0);
        const targetLatticeY = 1.0 + (audioTreble * 3.0);
        const targetLatticeZ = 1.0 + (rms * 1.5);

        // Interpolazione verso il target di deformazione basato sul volume continuo
        latticeX += (targetLatticeX - latticeX) * (dt * 15.0);
        latticeY += (targetLatticeY - latticeY) * (dt * 15.0);
        latticeZ += (targetLatticeZ - latticeZ) * (dt * 15.0);

        // Climax Auto-Zoom: la camera reagisce al volume
        if (rms > 0.55) autoZoom += (-600 - autoZoom) * (dt * 3.0);
        else autoZoom += (0 - autoZoom) * (dt * 1.5);

        targetZoom = baseZoom + autoZoom;
    }

    function sysLoop(now) {
        let dt = (now - lastTime) / 1000.0;

        // LIMITATORE ANTI-ESPLOSIONE: se il tempo trascorso è troppo, lo cappiamo a 50ms
        if (dt > 0.05) dt = 0.05;

        lastTime = now;

        // Incremento rotazione continua proporzionata al tempo reale (Elicoidale)
        const baseSpeed = EARTH_ANGULAR_VELOCITY * TIME_SCALE * dt;
        autoRotationY += baseSpeed;
        autoRotationX += baseSpeed * 0.618; // Precessione basata su Phi
        autoRotationZ += baseSpeed * 0.382; // Avvitamento lento

        // --- AGGIORNAMENTO ORBITA MOUSE ---
        currentOrbitX += (targetOrbitX - currentOrbitX) * (dt * 5.0);
        currentOrbitY += (targetOrbitY - currentOrbitY) * (dt * 5.0);
        mouseZoom += (targetZoom - mouseZoom) * (dt * 5.0);

        if (analyser && dataArray) {
            analyser.getFloatFrequencyData(dataArray);
            if (analyserL && dataArrayL) analyserL.getFloatFrequencyData(dataArrayL);
            if (analyserR && dataArrayR) analyserR.getFloatFrequencyData(dataArrayR);

            // Mappatura da Decibel (Float) a spazio lineare [0.0 - 255.0]
            // Preserviamo la precisione millimetrica della virgola mobile
            const minDb = analyser.minDecibels;
            const maxDb = analyser.maxDecibels;
            const rangeScale = 255.0 / (maxDb - minDb);
            
            if (!prevDataArray || prevDataArray.length !== dataArray.length) {
                prevDataArray = new Float32Array(dataArray.length);
            }

            // BUG FIX #2: Loop unico — normalizzazione dB, spectral flux, band sums, RMS, centroide
            // Sostituisce 3 loop sequenziali su 1024 elementi con una singola passata O(n).
            let currentKickFlux = 0;
            let currentSnareFlux = 0;
            let sum = 0, subSum = 0, kickSum = 0, lowMidSum = 0, snareSnapSum = 0, hiHatSum = 0;
            let sumL = 0, sumR = 0;
            let maxVal = 0, dominantBin = 0;
            let weightedBinSum = 0, totalMagnitude = 0;

            // Leggi i limiti calibrati una sola volta per frame (evita property lookup ×1024)
            const _subLo      = SPEC.subLo,      _subHi      = SPEC.subHi;
            const _kickLo     = SPEC.kickLo,     _kickHi     = SPEC.kickHi;
            const _kickFLo    = SPEC.kickFluxLo, _kickFHi    = SPEC.kickFluxHi;
            const _lowMidLo   = SPEC.lowMidLo,   _lowMidHi   = SPEC.lowMidHi;
            const _snareLo    = SPEC.snareLo,     _snareHi    = SPEC.snareHi;
            const _snareFLo   = SPEC.snareFluxLo,_snareFHi   = SPEC.snareFluxHi;
            const _hiHatLo    = SPEC.hiHatLo,     _hiHatHi    = SPEC.hiHatHi;

            for (let i = 0; i < dataArray.length; i++) {
                // 1. Normalizzazione dB → lineare
                let val = Math.max(0.0, (dataArray[i] - minDb) * rangeScale);
                const valL_raw = dataArrayL ? Math.max(0.0, (dataArrayL[i] - minDb) * rangeScale) : val;
                const valR_raw = dataArrayR ? Math.max(0.0, (dataArrayR[i] - minDb) * rangeScale) : val;

                // 2. Spectral Flux (Onset detection) — bin calibrati da Hz reali
                const diff = val - prevDataArray[i];
                if (diff > 0) {
                    if (i >= _kickFLo  && i <= _kickFHi)  currentKickFlux  += diff;
                    if (i >= _snareFLo && i <= _snareFHi) currentSnareFlux += diff;
                }
                prevDataArray[i] = val;
                dataArray[i] = val;
                if (dataArrayL) dataArrayL[i] = valL_raw;
                if (dataArrayR) dataArrayR[i] = valR_raw;

                // 3. Band sums + RMS accumulator — bande calibrate
                sum += val;
                if (val > maxVal) { maxVal = val; dominantBin = i; }
                if (i >= _subLo    && i <= _subHi)    subSum      += val; // SUB    (20–40 Hz)
                if (i >= _kickLo   && i <= _kickHi)   kickSum     += val; // KICK   (60–120 Hz)
                if (i >= _lowMidLo && i <= _lowMidHi) lowMidSum   += val; // LOWMID (150–300 Hz)
                if (i >= _snareLo  && i <= _snareHi)  snareSnapSum += val; // SNARE  (2–4.5 kHz)
                if (i >= _hiHatLo  && i <= _hiHatHi)  hiHatSum    += val; // HI-HAT (8–12 kHz)
                if (dataArrayL) sumL += valL_raw;
                if (dataArrayR) sumR += valR_raw;

                // 4. Centroide spettrale (accumulatori pesati)
                weightedBinSum += i * val;
                totalMagnitude += val;
            }

            kickFlux  = currentKickFlux  / SPEC.kickFluxN;
            snareFlux = currentSnareFlux / SPEC.snareN;

            dominantHue = (dominantBin * 3 + now * 0.05) % 360;
            let rawRms = Math.sqrt(sum / dataArray.length) / 255.0;
            let rmsL = dataArrayL ? (Math.sqrt(sumL / dataArrayL.length) / 255.0) : rawRms;
            let rmsR = dataArrayR ? (Math.sqrt(sumR / dataArrayR.length) / 255.0) : rawRms;

            // Normalizzazione dinamica: i divisori seguono il numero reale di bin per banda
            const _bassN   = (SPEC.subHi    - SPEC.subLo    + 1) + (SPEC.kickHi  - SPEC.kickLo  + 1);
            const _midN    = SPEC.lowMidHi  - SPEC.lowMidLo + 1;
            const _trebleN = SPEC.hiHatHi   - SPEC.hiHatLo  + 1;
            let rawBass = Math.min(1.0, (subSum + kickSum) / (_bassN * 255.0));
            let bassEnergy = rawBass;
            let rms = rawRms;

            const rawMid     = lowMidSum / (_midN    * 255.0);
            const rawTreble  = hiHatSum  / (_trebleN * 255.0);
            const rawCentroid = totalMagnitude > 0 ? weightedBinSum / totalMagnitude / dataArray.length : 0.5;
            const rawStereoWidth = Math.abs(rmsL - rmsR);

            // Smooth all features (no jitter)
            audioBass += (rawBass - audioBass) * (dt * 12.0);
            audioMid += (rawMid - audioMid) * (dt * 10.0);
            audioTreble += (rawTreble - audioTreble) * (dt * 10.0);
            audioSpectralCentroid += (rawCentroid - audioSpectralCentroid) * (dt * 8.0);
            audioStereoWidth += (rawStereoWidth - audioStereoWidth) * (dt * 10.0);

            // Kick pulse: decays fast, fired on beat
            kickPulse *= Math.max(0, 1.0 - dt * 8.0);

            updateAudioLogic(dataArray, now, dt, rms);

            // ---- TRANSIENT BEAT DETECTION (Spectral Flux) ----
            let isBeat = false;
            // Il sistema ora percepisce unicamente i colpi fisici veri e propri
            if (kickFlux > beatHistory * 1.5 && kickFlux > 15.0 && (now - lastBeatTime) > 120) {
                isBeat = true;
                lastBeatTime = now;
                beatCount++;
                targetGeometryIdx = 0;
                kickPulse = Math.min(1.0, kickPulse + 0.6); // Accumula impulso radiale
                
                // Grid Snapping estremo sui calci potenti
                if (kickFlux > 25.0) {
                    gridSnapFrames = 4;
                }
                
                // --- CINEMATOGRAFIA AUDIO-REATTIVA (Camera Snap) ---
                if (kickFlux > 30.0 && (now - lastCameraCutTime) > 800) {
                    lastCameraCutTime = now;
                    // Taglio di camera chirurgico su angoli rigidi (Orthographic feel)
                    const cutAngles = [Math.PI/2, Math.PI, -Math.PI/2, 0];
                    cameraCutOffsetY = cutAngles[Math.floor(Math.random() * cutAngles.length)];
                    if (Math.random() > 0.6) {
                        cameraCutOffsetX = (Math.random() > 0.5 ? Math.PI/4 : -Math.PI/4);
                    } else {
                        cameraCutOffsetX = 0;
                    }
                    // Zoom strappato
                    autoZoom += 800;
                }
            }
            beatHistory += (kickFlux - beatHistory) * (dt * 15.0);

            // ---- LOCK-IN ARCHITETTURALE (ANTI-NEBBIA) ----
            if (!window.morphHold) window.morphHold = 0;

            // Selezioniamo i valori reali o li forziamo a 0 durante la transizione
            let activeRms = window.isTransitioningFS ? 0 : rms;
            let activeBass = window.isTransitioningFS ? 0 : bassEnergy;

            // Se la musica pompa forte, blocchiamo la geometria 3D (usando le variabili filtrate)
            if (activeRms > 0.12 || activeBass > 0.25) {
                window.morphHold = 15; // Ritorno al logo più rapido nei silenzi
            }
            if (window.morphHold > 0) {
                window.morphHold--;
            }

            // targetMorph è binario: 1.0 (Scultura perfetta) o 0.0 (Logo perfetto)
            let targetMorph = (window.morphHold > 0) ? 1.0 : 0.0;

            // Transizione Immediata / Istantanea (Abolito il Morphing Fluido)
            smoothedMorph = targetMorph;

            // Il controllo 'userGlyphScale' influisce solo sulla scultura 3D animata.
            // Quando smoothedMorph è 0 (Logo), animScale è 1.0 (dimensione naturale).
            // Quando smoothedMorph è 1 (3D), animScale è userGlyphScale.
            const animScale = 1.0 + (userGlyphScale - 1.0) * smoothedMorph;

            const winW = 1920;
            const winH = 1080;

            // BUG FIX #8: PHI_LOCAL rimosso — usa PHI dal modulo
            const transitionPulse = Math.sin(smoothedMorph * Math.PI);

            // Pre-compute frame rotation matrix (elimina 360K chiamate Math.cos/sin)
            const tremor = rms * 0.2;
            const fRotZ = autoRotationZ + cameraCutOffsetZ + (Math.sin(now * 0.02) * tremor);
            const fRotY = autoRotationY + currentOrbitY + cameraCutOffsetY + (Math.sin(now * 0.01) * tremor);
            const fRotX = 0.41 + autoRotationX + currentOrbitX + cameraCutOffsetX + (Math.cos(now * 0.015) * tremor);
            fGcZ = Math.cos(fRotZ); fGsZ = Math.sin(fRotZ);
            fGcY = Math.cos(fRotY); fGsY = Math.sin(fRotY);
            fGcX = Math.cos(fRotX); fGsX = Math.sin(fRotX);
            fPump = 0.8 + (rms * 1.2);
            fCamZ = isNaN(mouseZoom) ? 1200 : mouseZoom;

            // BUG FIX #3: Chiamata unica per frame (era dentro getGantzGrafTarget ×60K)
            if (dataArray) updateBlockExtrusions();

            // BUG FIX #5 (corretto): _defaultShape pre-allocato per il caso logo (smoothedMorph=0)
            // In 3D mode la geometry fn restituisce geomOut (già pre-allocato a livello modulo) — zero alloc.
            const _defaultShape = { x: 0, y: 0, depth: 1.0, isSilhouette: false, layerType: 'mesh', nx: 0, ny: 0, nz: 0 };

            for (let i = 0; i < MAX_PARTICLES; i++) {
                const idx = i * STRIDE;
                let finalShape = _defaultShape; // default: nessuna alloc, punta al sentinel

                if (i < activeParticles) {
                    const logo = logoTargets[i];
                    if (!logo) continue;

                    const chunkSize = 200;
                    const chunkId = Math.floor(i / chunkSize);
                    const bin = (chunkId * 7) % dataArray.length;
                    const audioSample = (dataArray[bin] - 128) / 128.0;
                    const rawAudio = Math.abs(audioSample);
                    const inChunkPos = i % chunkSize;
                    const particleType = inChunkPos % 4;

                    // Decimazione per il logo: usiamo il 50% delle particelle per altissima definizione
                    const isNeededForLogo = (i % 2 === 0);
                    // Niente decimazione aggressiva: manteniamo alta definizione ovunque
                    // Se lagga, riduciamo leggermente solo quando siamo completamente immersi
                    let lodMod = 1;
                    if (mouseZoom < 800) lodMod = 2; // Quando zoomiamo dentro, disegniamo 1 su 2

                    const isVisibleIn3D = (i % lodMod === 0);

                    let tx = logo.x;
                    let ty = logo.y;
                    let depthScale = 1.0;

                    // --- OTTIMIZZAZIONE ESTREMA DEL RIENTRO ---
                    // Se smoothedMorph è sceso sotto una certa soglia (es. 0.2), 
                    // SMETTIAMO completamente di calcolare il caos spaziale e il 3D.
                    // Le particelle scivolano dritte verso il logo. Zero lag.

                    if (smoothedMorph > 0.0) {
                        // geometries[x]() scrive e restituisce geomOut (pre-allocato a livello modulo — zero alloc)
                        finalShape = geometries[currentGeometryIdx](i, activeParticles, now, winW, winH, rms, audioSample, rmsL, rmsR);
                        depthScale = finalShape.depth;

                        const pr1 = ((i * 12.9898) % 1.0);

                        if (smoothedMorph > 0.2) {
                            const pr2 = ((i * 78.2330) % 1.0);
                            const pr3 = ((i * 45.1640) % 1.0);

                            // Curva di accelerazione più rapida
                            let organicMorph = Math.pow(smoothedMorph, 0.5 + (pr1 * 1.5));

                            // --- FLUIDODINAMICA A SCIAME (SWARM FLOW) ---
                            // Sostituiamo la nebulosa rigida con un movimento organico e continuo.
                            // Le particelle formano il solido ma fluttuano costantemente attorno al loro target, come api.
                            
                            const timeSec = now * 0.001;
                            
                            // Onde sfasate per simulare un moto fluido/browniano per ogni singola particella
                            const flowX = Math.sin(timeSec * 1.3 + i * 0.11) * Math.cos(timeSec * 0.7 + i * 0.07);
                            const flowY = Math.cos(timeSec * 1.1 + i * 0.17) * Math.sin(timeSec * 0.9 + i * 0.05);
                            
                            // L'ampiezza dello sciame è viva: palpita con l'energia audio (rms)
                            // Quando l'audio è calmo, vibrano di pochi pixel. Sui bassi potenti, esplodono e rientrano.
                            const baseSwarm = 5.0; // Vibrazione minima costante
                            const audioSwarm = (rms * 180.0) * pr2; // Espansione audio-reattiva
                            const swarmAmplitude = baseSwarm + audioSwarm;
                            
                            const swarmOffsetX = finalShape.isSilhouette ? 0 : flowX * swarmAmplitude;
                            const swarmOffsetY = finalShape.isSilhouette ? 0 : flowY * swarmAmplitude;

                            // GLITCH SLICING: Sui picchi estremi di RMS spostiamo bruscamente interi blocchi
                            const glitchShift = (rms > 0.35) ? (Math.sin(i * 0.5 + now * 0.1) * rms * 200.0) : 0;

                            tx = logo.x + (finalShape.x - logo.x) * organicMorph + swarmOffsetX + glitchShift;
                            ty = logo.y + (finalShape.y - logo.y) * organicMorph + swarmOffsetY;
                        } else {
                            // INTERPOLAZIONE DIRETTA CON EFFETTO SCIAME (Vortex)
                            let organicMorph = Math.pow(smoothedMorph * 5.0, 0.7); // Curva più morbida

                            // Aggiungiamo un vortice procedurale basato sull'indice della particella
                            const swirlAngle = now * 0.002 + (i * PHI);
                            const swirlRadius = smoothedMorph * 400.0; // Il raggio diminuisce man mano che arrivano al logo

                            const swirlX = Math.cos(swirlAngle) * swirlRadius;
                            const swirlY = Math.sin(swirlAngle) * swirlRadius;

                            // Calcoliamo la posizione di rientro aggiungendo la turbolenza dello sciame
                            tx = logo.x + (finalShape.x - logo.x) * organicMorph + swirlX;
                            ty = logo.y + (finalShape.y - logo.y) * organicMorph + swirlY;
                        }
                    }

                    // --- QUANTIZZAZIONE SPAZIALE (Grid Snapping) ---
                    if (gridSnapFrames > 0 && !logo.isCoreLogo) {
                        const gridSize = 16;
                        tx = Math.round(tx / gridSize) * gridSize;
                        ty = Math.round(ty / gridSize) * gridSize;
                    }

                    tx = Math.max(20, Math.min(winW - 20, tx));
                    ty = Math.max(20, Math.min(winH - 20, ty));

                    currentSwarmData[idx + IDX_ACTIVE] = 1;
                    currentSwarmData[idx + IDX_TX] = tx;
                    currentSwarmData[idx + IDX_TY] = ty;

                    // --- GESTIONE OPACITÀ E DECIMAZIONE ---
                    if (smoothedMorph < 0.1) {
                        // STATO LOGO: Reset Priorità e Shading per rendering 2D ambra puro (Fix Backup)
                        currentSwarmData[idx + IDX_PRIO] = 100;
                        currentSwarmData[idx + IDX_REACT] = 1.8; // Gravità magnetica brutale per il rientro (Saturazione del Vuoto)

                        // STATO LOGO: Disegniamo SOLO le particelle "Core" che formano il vero testo
                        if (logo.isCoreLogo) {
                            currentSwarmData[idx + IDX_T_OPACITY] = 1.0;
                            currentSwarmData[idx + IDX_SCALE] = 0.15 * animScale;
                            currentGlyphIDs[i] = atlasFastMap[logo.originalChar] || dotGlyphID;
                        } else {
                            // Le decine di migliaia di particelle in eccesso svaniscono per non creare overdraw bianco
                            currentSwarmData[idx + IDX_T_OPACITY] = 0.0;
                        }
                    } else {
                        // STATO 3D SCULTURA — Tutte le 60K particelle contribuiscono
                        {
                            const timeFlow = now * 0.02;
                            const audioTurbulence = rawAudio * 20.0;
                            const dataHash = Math.floor((i * 0.3) + timeFlow + audioTurbulence);

                            const freqVal = (dataArray[bin] || 0) / 255.0;
                            let localBrightness, finalScaleMod;

                            // --- SHADING 3D REALE (Con protezione per il Logo) ---
                            const isLogoState = (smoothedMorph < 0.2); // Siamo in modalità Logo

                            const lightPos = now * 0.0008;
                            const lxL = Math.cos(lightPos), lyL = Math.sin(lightPos), lzL = Math.sin(lightPos * 0.5);

                            // Per il logo usiamo una normale frontale fissa per evitare buchi d'ombra
                            const effNX = isLogoState ? 0 : finalShape.nx;
                            const effNY = isLogoState ? 0 : finalShape.ny;
                            const effNZ = isLogoState ? 1 : finalShape.nz;

                            const dot = (effNX * lxL + effNY * lyL + effNZ * lzL);
                            const lightIntensity = isLogoState ? 1.0 : Math.max(0.1, (dot + 1.0) * 0.5);

                            // --- BACKFACE CULLING / OCCLUSION ---
                            const viewDot = effNZ;
                            const isBackface = (!isLogoState && viewDot < -0.1);

                            // --- RIM LIGHTING (Luce di Profilo) ---
                            // La luce colpisce i bordi quando la normale è perpendicolare alla camera
                            const rim = 1.0 - Math.abs(viewDot);
                            const rimLight = Math.pow(rim, 3.0) * (0.5 + rms * 2.0);

                            // GLITCH DI DISLOCAZIONE (Spostamento layer sui picchi)
                            // --- ESTRAZIONE AUDIO A ZERO LATENZA (bin calibrati da Hz) ---
                            const _kiLo = SPEC.kickInstLo, _kiHi = SPEC.kickInstHi, _kiN = SPEC.kickInstN;
                            let _kickInstSum = 0;
                            for (let _k = _kiLo; _k <= _kiHi; _k++) _kickInstSum += (dataArray[_k] || 0);
                            const instantKick = _kickInstSum / (_kiN * 255.0);
                            const isHardKick = instantKick > 0.60;

                            // --- MICRO-GLITCH AD ALTA FREQUENZA (bin hi-hat calibrato) ---
                            const _hg = SPEC.hiHatGlitch;
                            const hiHatVal = ((dataArray[_hg-1]||0) + (dataArray[_hg]||0) + (dataArray[_hg+1]||0)) / (3 * 255.0);

                            // GLITCH DI DISLOCAZIONE (Spostamento layer)
                            let glitchX = 0, glitchY = 0;
                            if (hiHatVal > 0.25 && finalShape.layerType === "structural" && dataHash % 5 === 0) {
                                glitchX += (Math.random() - 0.5) * hiHatVal * 150.0;
                                glitchY += (Math.random() - 0.5) * hiHatVal * 150.0;
                            }

                            if (particleType === 0) {
                                if (isLogoState) {
                                    localBrightness = 1.2 * lightIntensity;
                                    finalScaleMod = 1.0;
                                } else {
                                    if (finalShape.layerType === "structural") {
                                        localBrightness = Math.min(1.8, (0.9 + (freqVal * 0.9) + rimLight) * lightIntensity);
                                        finalScaleMod = 1.35;
                                    } else {
                                        localBrightness = Math.min(1.0, (0.3 + (freqVal * 0.5) + rimLight * 0.5) * lightIntensity);
                                        finalScaleMod = 0.9;
                                    }
                                }
                            } else {
                                if (isLogoState) {
                                    localBrightness = 1.0 * lightIntensity;
                                    finalScaleMod = 0.85;
                                } else {
                                    if (finalShape.layerType === "structural") {
                                        localBrightness = Math.min(1.4, (0.7 + (freqVal * 0.6) + rimLight) * lightIntensity);
                                        finalScaleMod = 1.0;
                                    } else {
                                        localBrightness = Math.min(0.8, (0.25 + (freqVal * 0.35) + rimLight * 0.4) * lightIntensity);
                                        finalScaleMod = 0.65;
                                    }
                                }
                            }

                            if (!isLogoState) {
                                const aoRadius = Math.sqrt(finalShape.nx * finalShape.nx + finalShape.ny * finalShape.ny);
                                localBrightness *= (0.4 + aoRadius * 0.6);
                                if (isBackface) {
                                    // --- BACKFACE ANNIHILATION ---
                                    // Se fa parte del solido opaco, nascondiamo la particella per salvare fill-rate GPU
                                    if (finalShape.layerType === "structural" || finalShape.layerType === "mesh") {
                                        currentSwarmData[idx + IDX_ACTIVE] = 0;
                                        localBrightness = 0.0;
                                    } else {
                                        localBrightness *= 0.15;
                                        finalScaleMod *= 0.5;
                                    }
                                }
                            }

                            const fogAmount = Math.pow(Math.max(0, Math.min(1, depthScale)), 1.5);
                            let zOpacity = fogAmount * localBrightness;
                            const zScale = Math.min(depthScale, 1.8);

                            // --- GANTZ GRAF ANTI-LAG & ZERO LATENCY ---
                            let activeGlyph;
                            let isSolidFace = false; 

                            // Estendiamo la rilevazione a qualsiasi transient forte (kick o rullanti secchi)
                            const isTransient = isHardKick || (hiHatVal > 0.6); 

                            if (isTransient && !isLogoState) {
                                // RESTAURIAMO L'ASCII: Scegliamo caratteri "densi" per formare l'illusione del solido
                                const heavyChars = ['#', '@', 'W', 'M', '8', '%'];
                                const randomHeavy = heavyChars[dataHash % heavyChars.length];
                                activeGlyph = atlasFastMap[randomHeavy.charCodeAt(0)] || dotGlyphID;
                                
                                if (finalShape.layerType === "mesh" && !isBackface) {
                                    if (i % 3 === 0) {
                                        finalScaleMod *= 3.8; 
                                        zOpacity = 1.0; 
                                        localBrightness = localBrightness * 2.5; // Alto contrasto per esaltare i volumi
                                        isSolidFace = true;
                                    } else {
                                        zOpacity = 0.0; 
                                    }
                                } else if (finalShape.layerType === "structural" && !isBackface) {
                                    finalScaleMod *= 1.8;
                                    zOpacity = 1.0;
                                }
                            } else {
                                if (!isLogoState) {
                                    // --- CORRUZIONE TIPOGRAFICA DINAMICA ---
                                    // Suoni ad alta frequenza molto forti (distorsione, rumore) corrompono il metallo
                                    const isGlitching = (audioTreble > 0.4 || rms > 0.4) && (dataHash % 3 === 0);
                                    
                                    if (isGlitching) {
                                        const glitchChars = ['!', '?', '\\', '/', '<', '>', '&', '%', '^'];
                                        activeGlyph = atlasFastMap[glitchChars[dataHash % glitchChars.length].charCodeAt(0)] || dotGlyphID;
                                    } else if (finalShape.layerType === "structural") {
                                        activeGlyph = atlasFastMap[structuralLibrary[dataHash % structuralLibrary.length]] || dotGlyphID;
                                    } else {
                                        activeGlyph = atlasFastMap[fillLibrary[dataHash % fillLibrary.length]] || dotGlyphID;
                                    }
                                } else {
                                    if (finalShape.layerType === "structural") {
                                        activeGlyph = atlasFastMap[structuralLibrary[dataHash % structuralLibrary.length]] || dotGlyphID;
                                    } else {
                                        activeGlyph = atlasFastMap[fillLibrary[dataHash % fillLibrary.length]] || dotGlyphID;
                                    }
                                }
                            }

                            // Assegnazione coordinate finali
                            currentSwarmData[idx + IDX_X] = finalShape.x + glitchX;
                            currentSwarmData[idx + IDX_Y] = finalShape.y + glitchY;
                            currentSwarmData[idx + IDX_Z] = depthScale; // TRASMETTIAMO LA PROFONDITÀ!
                            
                            currentSwarmData[idx + IDX_T_OPACITY] = zOpacity;
                            currentSwarmData[idx + IDX_SCALE] = (0.5 + (rms * 0.6)) * zScale * animScale * finalScaleMod;

                            if (isLogoState) {
                                const lChar = logoTargets[i] ? logoTargets[i].originalChar : 0;
                                currentGlyphIDs[i] = lChar ? (atlasFastMap[lChar] || dotGlyphID) : activeGlyph;
                            } else {
                                currentGlyphIDs[i] = activeGlyph;
                            }

                            // --- CROMATISMO STEREO E SHADER ---
                            const valL = (dataArrayL && dataArrayL[bin]) ? dataArrayL[bin] : 0;
                            const valR = (dataArrayR && dataArrayR[bin]) ? dataArrayR[bin] : 0;
                            let stereoHue = dominantHue;
                            const freqOffset = (bin / 50.0) * 60.0; 
                            
                            if (valL > valR + 10) {
                                stereoHue = 180 + freqOffset; // Ciano / Blu
                            } else if (valR > valL + 10) {
                                stereoHue = 0 + freqOffset; // Rosso / Arancio
                            } else {
                                stereoHue = 100 + freqOffset; // Smeraldo
                            }
                            
                            let encodedPrio;

                            if (isSolidFace) {
                                // SHADER METALLICO: Trasferiamo la luminosità reale al worker (da 5% a 90%)
                                let luma = Math.min(90, Math.max(5, Math.floor(localBrightness * 45)));
                                // Un valore PRIO >= 2000 farà scattare il nuovo render vettoriale nel worker
                                encodedPrio = 2000 + Math.floor(stereoHue % 360) + (luma * 1000);
                            } else {
                                encodedPrio = 1000 + Math.floor(stereoHue % 360);
                                if (finalShape.layerType === "structural" && (1.0 - Math.abs(effNZ)) > 0.7) {
                                    encodedPrio = 1000 + Math.floor((stereoHue + 30) % 360);
                                }
                                if (rms > 0.55 && dataHash % 5 === 0) {
                                    encodedPrio = 1000 + 60; 
                                }
                            }

                            currentSwarmData[idx + IDX_PRIO] = encodedPrio;
                            currentSwarmData[idx + IDX_REACT] = (smoothedMorph > 0.99) ? 1.0 : (0.05 + (smoothedMorph * 0.5));
                        }
                    }

                } else {
                    currentSwarmData[idx + IDX_ACTIVE] = 0;
                    currentSwarmData[idx + IDX_T_OPACITY] = 0.0;
                }
            }

            if (invertFrames > 0) invertFrames--;
            if (gridSnapFrames > 0) gridSnapFrames--;

            swarmWorkerInstance.postMessage({
                type: 'UPDATE_STATE',
                // BUG FIX #4: isLogoMode segnala al worker di saltare il Z-sort O(n log n)
                // quando siamo in stato logo 2D (profondità irrilevante)
                data: { rms: rms * 2.0, prob: bassEnergy, appState: 'IDLE', invertCanvas: (invertFrames > 0), isLogoMode: (smoothedMorph < 0.1) }
            });

            swarmWorkerInstance.postMessage({ type: 'TICK' });

        }
    }
}

document.getElementById('start-btn').addEventListener('click', startAudio);

document.getElementById('audio-input-select').addEventListener('change', async () => {
    if (audioCtx) {
        await audioCtx.close();
        audioCtx = null;
        startAudio();
    }
});

window.projectorWorker = null;

let isColorMode = true;
const btnColorMode = document.getElementById('btn-color-mode');
btnColorMode.addEventListener('click', () => {
    isColorMode = !isColorMode;
    btnColorMode.innerText = isColorMode ? '[ COLOR: ON ]' : '[ COLOR: OFF ]';
    if (swarmWorkerInstance) {
        swarmWorkerInstance.postMessage({
            type: 'UPDATE_STATE',
            data: { colorMode: isColorMode }
        });
    }
});

document.getElementById('btn-projector').addEventListener('click', () => {
    const canvas = document.getElementById('swarm-matrix');
    
    // Attiviamo la modalità silenzio temporaneo
    window.isTransitioningFS = true; 

    if (document.fullscreenElement || document.webkitFullscreenElement) {
        (document.exitFullscreen || document.webkitExitFullscreen).call(document);
    } else {
        const reqFS = canvas.requestFullscreen || canvas.webkitRequestFullscreen;
        if (reqFS) {
            const promise = reqFS.call(canvas);
            if (promise && promise.catch) promise.catch(e => console.error(e));
        }
    }
});

function handleFullscreenState() {
    window.isTransitioningFS = true;
    setTimeout(() => {
        window.isTransitioningFS = false;
    }, 150);

    // Controlla se siamo in HTML5 Fullscreen
    const isHTML5FS = !!(document.fullscreenElement || document.webkitFullscreenElement);
    
    if (isHTML5FS) {
        document.body.classList.add('is-fullscreen');
    } else {
        document.body.classList.remove('is-fullscreen');
    }
}

document.addEventListener('fullscreenchange', handleFullscreenState);
document.addEventListener('webkitfullscreenchange', handleFullscreenState);

// Saturazione (Zero Waste): Intercetta anche il fullscreen nativo di macOS (tasto verde)
window.addEventListener('resize', () => {
    // Se la finestra occupa l'intero schermo logico (o quasi, tolleranza 5px per i bordi)
    if (window.innerWidth >= window.screen.width - 5 && window.innerHeight >= window.screen.height - 5) {
        document.body.classList.add('is-fullscreen');
    } else if (!document.fullscreenElement && !document.webkitFullscreenElement) {
        document.body.classList.remove('is-fullscreen');
    }
});

