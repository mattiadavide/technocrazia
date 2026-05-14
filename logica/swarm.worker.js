import {
    PHI, SWARM_SIZE, STRIDE,
    IDX_X, IDX_Y, IDX_TX, IDX_TY,
    IDX_OPACITY, IDX_ACTIVE, IDX_PRIO, IDX_REACT, IDX_SCALE, IDX_T_OPACITY, IDX_Z
} from './swarm_core.js';
const PHI_POW_15_INV = 1.0 / Math.pow(PHI, 15.0);
const PHI_POW_14_5_INV = 1.0 / Math.pow(PHI, 14.5);
const PHI_POW_14_INV = 1.0 / Math.pow(PHI, 14.0);

const PHI_POW_11_INV = 1.0 / Math.pow(PHI, 11.0);
const PHI_POW_10_5_INV = 1.0 / Math.pow(PHI, 10.5);
const PHI_POW_6_INV = 1.0 / Math.pow(PHI, 6.0);
const PHI_POW_4_INV = 1.0 / Math.pow(PHI, 4.0);
const PHI_POW_3_INV = 1.0 / Math.pow(PHI, 3.0);
const PHI_POW_2_INV = 1.0 / Math.pow(PHI, 2.0);
const PHI_POW_0_5_INV = 1.0 / Math.pow(PHI, 0.5);
const PHI_POW_11 = Math.pow(PHI, 11.0);
const PHI_POW_8 = Math.pow(PHI, 8.0);
const PHI_POW_6 = Math.pow(PHI, 6.0);
const PHI_POW_5 = Math.pow(PHI, 5.0);
const PHI_POW_3 = Math.pow(PHI, 3.0);
const PHI_POW_3_5_INV = 1.0 / Math.pow(PHI, 3.5);
const SQRT_PHI = Math.sqrt(PHI);
const DISPERSION_INV = 1.0 / (200.0 * PHI);
const PHI_INV = 1.0 / PHI;
const GLITCH_RATE_INV = 1.0 / (25.0 * PHI);
const MAX_PARTICLES = SWARM_SIZE;
const atomHashArray = new Float32Array(MAX_PARTICLES);
for (let i = 0; i < MAX_PARTICLES; i++) {
    atomHashArray[i] = ((i * PHI) % 1.0);
}
const LUT_SIZE = 1024;
const LUT_MASK = LUT_SIZE - 1;
const SINE_LUT = new Float32Array(LUT_SIZE);
for (let j = 0; j < LUT_SIZE; j++) {
    SINE_LUT[j] = Math.sin((j / LUT_SIZE) * Math.PI * 2);
}
const COLOR_MAIN = "rgb(255, 176, 0)";
const COLOR_STATIC = "rgb(16, 16, 16)";
const COLOR_LUT = [
    "rgb(0, 0, 255)", "rgb(0, 255, 0)", "rgb(0, 255, 255)",
    "rgb(255, 0, 0)", "rgb(255, 0, 255)", "rgb(255, 255, 0)", "rgb(255, 255, 255)"
];
const colorPhaseR = new Int32Array(MAX_PARTICLES);
const colorPhaseG = new Int32Array(MAX_PARTICLES);
const colorPhaseB = new Int32Array(MAX_PARTICLES);
for (let i = 0; i < MAX_PARTICLES; i++) {
    colorPhaseR[i] = Math.floor((i * 137.5) * (LUT_SIZE / (Math.PI * 2))) % LUT_SIZE;
    colorPhaseG[i] = Math.floor((i * 342.1) * (LUT_SIZE / (Math.PI * 2))) % LUT_SIZE;
    colorPhaseB[i] = Math.floor((i * 512.3) * (LUT_SIZE / (Math.PI * 2))) % LUT_SIZE;
}
let canvas = null;
let ctx = null;
let atlasBitmap = null;
let coloredAtlases = [];
let atlasInverted = null;
let atlasLookup = [];
let dpr = 1;
let dotGlyphID = 0;
let swarmData = null;
let glyphIDs = null;
let syncArray = null;
const velocities = new Float32Array(MAX_PARTICLES * 2);
const staticNoise = new Float32Array(MAX_PARTICLES);
for (let i = 0; i < MAX_PARTICLES; i++) {
    staticNoise[i] = Math.sin(i * PHI) * PHI_POW_3_INV;
}
const lockTimeMs = new Float32Array(MAX_PARTICLES);
let transitionStartTime = 0;
let isTransitioning = false;
const phaseCos = new Float32Array(MAX_PARTICLES);
const phaseSin = new Float32Array(MAX_PARTICLES);
for (let i = 0; i < MAX_PARTICLES; i++) {
    const B = i * PHI_POW_14_INV;
    phaseCos[i] = Math.cos(B);
    phaseSin[i] = Math.sin(B);
}
let renderState = { rms: 0, prob: 0, appState: 'BOOT', width: 0, height: 0, isTranscribing: false, colorMode: true, isLogoMode: false };
let lastTime = performance.now();
let isLoopRunning = false;

// FIX #7: HSL LUT pre-calcolata (36 hue × 91 luma) — zero string alloc per particella in 3D mode
// Struttura: HSL_BG_LUT[hueIndex][luma] = stringa CSS "hsl(H, 60%, L%)"
const HSL_BG_LUT = new Array(36);
for (let hi = 0; hi < 36; hi++) {
    HSL_BG_LUT[hi] = new Array(91);
    for (let l = 0; l <= 90; l++) {
        HSL_BG_LUT[hi][l] = `hsl(${hi * 10}, 60%, ${Math.max(1, l * 0.1).toFixed(1)}%)`;
    }
}

// ARRAY PER IL Z-SORTING
const radixBuffer = new Float64Array(MAX_PARTICLES);
const drawOrder = new Uint32Array(MAX_PARTICLES);
for(let i = 0; i < MAX_PARTICLES; i++) drawOrder[i] = i;
function wakeUpLoop() {
    if (!isLoopRunning && ctx) {
        isLoopRunning = true;
        lastTime = performance.now();
        requestAnimationFrame(loop);
    }
}
self.onmessage = (e) => {
    const { type, data } = e.data;
    switch (type) {
        case 'INIT':
            canvas = data.canvas;
            ctx = canvas.getContext('2d', { alpha: true, desynchronized: true });
            ctx.imageSmoothingEnabled = false;
            dpr = data.dpr || 1;
            ctx.setTransform(1, 0, 0, 1, 0, 0);
            ctx.scale(dpr, dpr);
            atlasBitmap = data.atlasBitmap;
            
            // GENERAZIONE ATLANTI COLORATI (Pre-rendering per performance estreme)
            // Creiamo 36 atlanti, ognuno tinto con una tonalità (hue) diversa
            coloredAtlases = [];
            for (let i = 0; i < 36; i++) {
                const off = new OffscreenCanvas(atlasBitmap.width, atlasBitmap.height);
                const octx = off.getContext('2d');
                octx.fillStyle = `hsl(${i * 10}, 100%, 65%)`; // Colore saturo e luminoso
                octx.fillRect(0, 0, off.width, off.height);
                octx.globalCompositeOperation = 'destination-in'; // Mantiene il colore solo dove c'è il testo bianco
                octx.drawImage(atlasBitmap, 0, 0);
                coloredAtlases.push(off);
            }
            
            // GENERAZIONE ATLANTE INVERTITO (Testo nero su sfondo trasparente) per performance estreme
            atlasInverted = new OffscreenCanvas(atlasBitmap.width, atlasBitmap.height);
            const ctxInv = atlasInverted.getContext('2d');
            ctxInv.fillStyle = 'black';
            ctxInv.fillRect(0, 0, atlasInverted.width, atlasInverted.height);
            ctxInv.globalCompositeOperation = 'destination-in';
            ctxInv.drawImage(atlasBitmap, 0, 0);
            
            atlasLookup = data.atlasLookup;
            dotGlyphID = data.dotGlyphID || 0;
            swarmData = new Float32Array(data.swarmBuffer);
            glyphIDs = new Uint16Array(data.glyphBuffer);
            syncArray = new Int32Array(data.syncBuffer);
            
            renderState.width = canvas.width / dpr;
            renderState.height = canvas.height / dpr;
            const cx = renderState.width / 2.0;
            const cy = renderState.height / 2.0;
            for (let i = 0; i < MAX_PARTICLES; i++) {
                swarmData[i * STRIDE + IDX_X] = cx;
                swarmData[i * STRIDE + IDX_Y] = cy;
                swarmData[i * STRIDE + IDX_TX] = cx;
                swarmData[i * STRIDE + IDX_TY] = cy;
            }
            wakeUpLoop();
            break;
        case 'UPDATE_STATE':
            Object.assign(renderState, data);
            break;

        case 'TICK':
            wakeUpLoop();
            break;

        case 'RESIZE':
            if (canvas) {
                dpr = data.dpr || 1;
                canvas.width = data.width * dpr;
                canvas.height = data.height * dpr;
                ctx.setTransform(1, 0, 0, 1, 0, 0);
                ctx.scale(dpr, dpr);
                renderState.width = data.width;
                renderState.height = data.height;
            }
            wakeUpLoop();
            break;
    }
};
let smoothedIntensity = 0;
const TARGET_FPS = 60;
const FRAME_MIN_TIME = 1000.0 / TARGET_FPS;
let lastDrawTime = 0;
function loop(now) {
    const elapsed = now - lastDrawTime;
    if (elapsed < FRAME_MIN_TIME) {
        if (isLoopRunning) requestAnimationFrame(loop);
        return;
    }
    lastDrawTime = now - (elapsed % FRAME_MIN_TIME);
    const dt = Math.min((now - lastTime) / 1000.0, 0.05);
    lastTime = now;
    if (!ctx || !swarmData) return requestAnimationFrame(loop);
    
    // --- STROBOSCOPIA ARCHITETTURALE (VJ Safe) ---
    // Il background DEVE rimanere sempre trasparente per il proiettore.
    ctx.clearRect(0, 0, renderState.width, renderState.height);
    ctx.globalCompositeOperation = 'source-over';
    let tgtI = renderState.rms * (20.0 * PHI);
    if (tgtI > SQRT_PHI) tgtI = SQRT_PHI;
    smoothedIntensity = tgtI > smoothedIntensity
        ? tgtI
        : smoothedIntensity + (tgtI - smoothedIntensity) * (1.0 / (PHI * 1.5));
    if (renderState.rms < 0.005) smoothedIntensity *= (1.0 / (PHI * 1.5));
    const audioEntropia = renderState.rms * (1.0 - renderState.prob);
    const A = now * PHI_POW_14_5_INV;
    const cosA = Math.cos(A);


    const sinA = Math.sin(A);
    const stateTime = now - transitionStartTime;
    const f1 = stateTime * PHI_POW_11_INV;
    const f2 = stateTime * PHI_POW_10_5_INV;
    const timeIdxR = ((now * 0.010) * (LUT_SIZE / (Math.PI * 2)) | 0) % LUT_SIZE;
    const timeIdxG = ((now * 0.015) * (LUT_SIZE / (Math.PI * 2)) | 0) % LUT_SIZE;
    const timeIdxB = ((now * 0.020) * (LUT_SIZE / (Math.PI * 2)) | 0) % LUT_SIZE;
    let isAnimating = false;
    let lastGlobalAlpha = -1.0;
    let lastFillStyle = "";
    const maxAtlasGlyphs = Math.min(40, atlasLookup.length);
    const isThinkingGlobal = (renderState.isTranscribing || renderState.appState === 'THINKING');
    
    const VIRTUAL_W = 1920;
    const VIRTUAL_H = 1080;
    const scaleX = renderState.width / VIRTUAL_W;
    const scaleY = renderState.height / VIRTUAL_H;
    const renderScale = Math.max(scaleX, scaleY);
    const offsetX = (renderState.width - VIRTUAL_W * renderScale) / 2;
    const offsetY = (renderState.height - VIRTUAL_H * renderScale) / 2;
    
    // BUG FIX #4: Z-sort condizionale — in logo-mode le particelle sono piatte,
    // il depth-order è irrilevante: saltiamo il sort O(n log n) su 60K elementi
    // (~960K confronti/frame eliminati durante lo stato logo).
    if (!renderState.isLogoMode) {
        // MODALITÀ 3D: Z-sort nativo per correttezza depth (necessario)
        for (let k = 0; k < MAX_PARTICLES; k++) {
            const zDepth = swarmData[k * STRIDE + IDX_Z];
            const zInt = Math.floor((zDepth + 10000.0) * 1000.0);
            radixBuffer[k] = zInt * 100000.0 + k;
        }
        radixBuffer.sort();
        for (let k = 0; k < MAX_PARTICLES; k++) {
            drawOrder[k] = radixBuffer[k] % 100000;
        }
    } else {
        // MODALITÀ LOGO 2D: ordine naturale, zero costo di sorting
        for (let k = 0; k < MAX_PARTICLES; k++) drawOrder[k] = k;
    }

    // Ciclo di render: usa drawOrder[] popolato dal sort condizionale sopra
    for (let k = 0; k < MAX_PARTICLES; k++) {
        const i = drawOrder[k];
        const idx = i * STRIDE;
        const vidx = i * 2;
        const active = swarmData[idx + IDX_ACTIVE];
        const targetOpacity = swarmData[idx + IDX_T_OPACITY];
        let currentOpacity = swarmData[idx + IDX_OPACITY];
        if (currentOpacity !== targetOpacity) {
            const diff = targetOpacity - currentOpacity;
            const decaySpeed = renderState.isTranscribing ? 3.5 : 15.0;
            currentOpacity += diff * (dt * (diff > 0 ? 8.0 : decaySpeed));
            if (Math.abs(diff) < 0.01) currentOpacity = targetOpacity;
            swarmData[idx + IDX_OPACITY] = currentOpacity;
            isAnimating = true; // Forza il render finché l'opacità cambia
        }
        const opacity = currentOpacity;
        if (active === 0 && opacity <= 0.01) continue;
        let currentX = swarmData[idx + IDX_X];
        let currentY = swarmData[idx + IDX_Y];
        const targetX = swarmData[idx + IDX_TX];
        const targetY = swarmData[idx + IDX_TY];
        const springPrio = swarmData[idx + IDX_REACT];
        const isLocked = !isTransitioning || (stateTime >= lockTimeMs[i]);
        let drawGlyphID = glyphIDs[i];
        let atomicScale = swarmData[idx + IDX_SCALE] || 1.0;
        let atomicOpacity = opacity;
        if (!isLocked) {
            if (active > 0) {
                atomicOpacity = 0.3 + (atomHashArray[i] * 0.7);
            } else {
                atomicOpacity = Math.max(0, atomicOpacity - PHI_POW_6_INV);
            }
            const timeToLock = Math.max(0.0, lockTimeMs[i] - stateTime);
            const tParam = timeToLock / lockTimeMs[i];
            const d2 = tParam * tParam;
            const forceThrow = 0.15 + (d2 * 0.85);
            const linearInertia = 1.0 / Math.pow(PHI, 1.5);
            const dx = (targetX - currentX) * forceThrow * linearInertia;
            const dy = (targetY - currentY) * forceThrow * linearInertia;
            velocities[vidx] = dx * (16.0 * Math.sqrt(PHI));
            velocities[vidx + 1] = dy * (16.0 * Math.sqrt(PHI));
            currentX += dx;
            currentY += dy;
            if (active > 0) {
                const atomHash = atomHashArray[i];
                const glitchFrame = (stateTime * GLITCH_RATE_INV + atomHash * 100.0) | 0;
                drawGlyphID = ((atomHash * 1000 | 0) + glitchFrame) % maxAtlasGlyphs;
            }
        } else {
            if (active === 2) swarmData[idx + IDX_ACTIVE] = 1;
            if (springPrio >= 2.0) { // Istantaneo solo per emergenze/reset
                currentX = targetX;
                currentY = targetY;
                velocities[vidx] = 0; velocities[vidx + 1] = 0;
            } else {
                // --- ASSEMBLAGGIO / DISASSEMBLAGGIO (Exponential Decay — Overdamped) ---
                // Sistema del 1° ordine: nessun overshoot matematicamente possibile.
                // Le particelle convergono sul target con decelerazione pura, come calamite.
                const dx = targetX - currentX;
                const dy = targetY - currentY;

                // Azzeriamo la velocità residua dall'eventuale stato 3D precedente.
                // Impedisce che l'inerzia del "lancio" contamini il rientro al logo.
                velocities[vidx] = 0;
                velocities[vidx + 1] = 0;

                // Velocità di convergenza: modulata da springPrio (1.8 = rientro al logo, fulmineo).
                const convergenceSpeed = 14.0 * Math.max(0.1, springPrio);
                // Clamp a 1.0 per evitare overshoot numerico (dt troppo grande = salto oltre il target)
                const t = Math.min(1.0, convergenceSpeed * dt);

                currentX += dx * t;
                currentY += dy * t;

                if (Math.abs(dx) > 0.5 || Math.abs(dy) > 0.5) {
                    isAnimating = true;
                } else {
                    // Snap finale: quando siamo a meno di mezzo pixel, agganciamo
                    currentX = targetX;
                    currentY = targetY;
                }
            }
        }
        swarmData[idx + IDX_X] = currentX;
        swarmData[idx + IDX_Y] = currentY;
        const isReactive = springPrio > 0;
        let jitter = 0;
        let noise = 0;
        if (isReactive) {
            const cosAplusB = cosA * phaseCos[i] - sinA * phaseSin[i];
            noise = staticNoise[i] + (cosAplusB * (audioEntropia * (6.0 * PHI)));
            // ZERO Jitter: i poligoni devono essere perfetti e affilatissimi (niente nebulosa)
            jitter = 0;
        }
        let drawX = Math.round(currentX * renderScale + offsetX + jitter);
        let drawY = Math.round(currentY * renderScale + offsetY + jitter);

        // Forced clamping (Antigravity Constraints)
        drawX = Math.max(0, Math.min(renderState.width, drawX));
        drawY = Math.max(0, Math.min(renderState.height, drawY));

        const prio = swarmData[idx + IDX_PRIO];
        const decryptDurationMs = 250.0 * Math.pow(PHI, 1.5);
        if (isLocked && atomicOpacity > 0.05) {
            let shouldMutate = false;
            let mutationRate = 15.0 * PHI;
            if (atomicScale > 1.0 && stateTime < lockTimeMs[i] + decryptDurationMs) {
                shouldMutate = true;
            }
            else if (isThinkingGlobal && prio === 150) {
                shouldMutate = true;
                mutationRate = 35.0 * PHI;
            }
            else if (renderState.appState === 'BOOT' && springPrio > 0) {
                shouldMutate = true;
            }
            if (shouldMutate && renderState.appState !== 'BOOT' && !isThinkingGlobal) {
                const scaledLockTime = lockTimeMs[i] * 0.75;
                const individualDelay = (atomicScale * PHI_POW_6) + scaledLockTime;
                if (stateTime > individualDelay) {
                    shouldMutate = false;
                }
            }
            if (shouldMutate) {
                if (prio !== 199 && prio !== 201 && prio !== 202) {
                    const invMutationRate = 1.0 / mutationRate;
                    const glitchFrame = (now * invMutationRate + atomHashArray[i] * 100.0) | 0;
                    drawGlyphID = ((atomHashArray[i] * 1000 | 0) + glitchFrame) % maxAtlasGlyphs;
                }
                isAnimating = true;
            }
        }
        const op = PHI_POW_0_5_INV + (prio / 100.0) + (noise * isReactive * PHI_POW_3_INV);
        const glyph = atlasLookup[drawGlyphID];
        if (glyph && atomicOpacity > 0.05) {
            const [au, av, aw, ah] = glyph;
            const seedPx = aw * 0.25;
            const targetSize = seedPx * PHI;
            const margin = targetSize * 2.0;
            if (drawX < -margin || drawX > renderState.width + margin ||
                drawY < -margin || drawY > renderState.height + margin) {
                isAnimating = true;
                continue;
            }
            // --- ALPHA QUANTIZATION ---
            // Arrotondiamo a 10 step per minimizzare i cambi di stato della GPU (es. 0.1, 0.2)
            const finalAlpha = Math.min(atomicOpacity * Math.min(op, 1.0), 1.0);
            const quantizedAlpha = Math.max(0.1, Math.round(finalAlpha * 10.0) / 10.0);
            
            if (lastGlobalAlpha !== quantizedAlpha) {
                ctx.globalAlpha = quantizedAlpha;
                lastGlobalAlpha = quantizedAlpha;
            }
            let targetFillStyle = COLOR_MAIN;
            
            if (prio >= 2000) {
                // --- SHADER 3D ASCII (FACCE PIENE + GLIFI) ---
                const hue = (prio - 2000) % 1000;
                const luma = Math.floor((prio - 2000) / 1000);
                const hueIndex = Math.floor(hue / 10) % 36;
                const activeAtlas = (renderState.colorMode !== false && coloredAtlases[hueIndex]) ? coloredAtlases[hueIndex] : atlasBitmap;
                
                // Dimensione aumentata per tappare perfettamente i buchi
                const finalSize = Math.max(1.0, (targetSize * atomicScale * renderScale * 1.1) | 0);
                const halfSize = finalSize * 0.5;
                
                if (renderState.invertCanvas) {
                    // Flash Negativo Materico VJ SAFE:
                    if (lastGlobalAlpha !== 1.0) {
                        ctx.globalAlpha = 1.0;
                        lastGlobalAlpha = 1.0;
                    }
                    ctx.fillStyle = 'rgb(255, 255, 255)';
                    ctx.fillRect((drawX - halfSize) | 0, (drawY - halfSize) | 0, finalSize, finalSize);
                    
                    ctx.drawImage(atlasInverted, au, av, aw, ah, (drawX - halfSize) | 0, (drawY - halfSize) | 0, finalSize, finalSize);
                } else {
                    // 1. OCCHLUSIONE: Disegniamo un fondo scuro per bloccare visivamente ciò che sta dietro
                    if (lastGlobalAlpha !== 1.0) {
                        ctx.globalAlpha = 1.0;
                        lastGlobalAlpha = 1.0;
                    }
                    if (renderState.colorMode !== false) {
                        // FIX #7: LUT lookup — zero alloc (era template literal per ogni particella)
                        const lutLuma = Math.min(90, Math.max(0, luma));
                        ctx.fillStyle = HSL_BG_LUT[hueIndex][lutLuma];
                    } else {
                        ctx.fillStyle = `hsl(38, 100%, ${Math.max(1, luma * 0.1)}%)`; // Amber monocromatico
                    }
                    ctx.fillRect((drawX - halfSize) | 0, (drawY - halfSize) | 0, finalSize, finalSize);
                    
                    // 2. ASCII TEXTURE: Disegniamo il carattere tipografico colorato con luminosità dinamica 3D
                    const lumaAlpha = Math.max(0.1, Math.round((luma / 100.0) * 10.0) / 10.0);
                    if (lastGlobalAlpha !== lumaAlpha) {
                        ctx.globalAlpha = lumaAlpha;
                        lastGlobalAlpha = lumaAlpha;
                    }
                    ctx.drawImage(activeAtlas, au, av, aw, ah, (drawX - halfSize) | 0, (drawY - halfSize) | 0, finalSize, finalSize);
                }
                
            } else if (prio >= 1000) {
                // MODALITÀ ASCII CROMATICA 3D (Usa gli atlanti pre-colorati)
                const hue = prio - 1000;
                const hueIndex = Math.floor(hue / 10) % 36;
                const activeAtlas = (renderState.colorMode !== false && coloredAtlases[hueIndex]) ? coloredAtlases[hueIndex] : atlasBitmap;
                                 
                const finalSize = Math.max(1.0, (targetSize * atomicScale * renderScale * 0.85) | 0);
                const halfSize = finalSize * 0.5;
                                 
                // Disegniamo il glifo GIA' COLORATO o Bianco Puro durante il flash
                if (renderState.invertCanvas) {
                    if (lastGlobalAlpha !== 1.0) {
                        ctx.globalAlpha = 1.0;
                        lastGlobalAlpha = 1.0;
                    }
                    ctx.drawImage(atlasBitmap, au, av, aw, ah, (drawX - halfSize) | 0, (drawY - halfSize) | 0, finalSize, finalSize);
                } else {
                    ctx.drawImage(activeAtlas, au, av, aw, ah, (drawX - halfSize) | 0, (drawY - halfSize) | 0, finalSize, finalSize);
                }
                             
            } else if (prio === 199 || prio === 200 || prio === 201) {
                const isStructuralCenter = (prio === 201);
                if (isStructuralCenter && !renderState.isTranscribing) {
                    targetFillStyle = COLOR_STATIC;
                } else {
                    if (Math.abs(lastGlobalAlpha - 1.0) > 0.005) {
                        ctx.globalAlpha = 1.0;
                        lastGlobalAlpha = 1.0;
                    }
                    if (prio === 199 && smoothedIntensity > 0.05) {
                        const rBit = SINE_LUT[(timeIdxR + colorPhaseR[i]) & LUT_MASK] > 0 ? 1 : 0;
                        const gBit = SINE_LUT[(timeIdxG + colorPhaseG[i]) & LUT_MASK] > 0 ? 1 : 0;
                        const bBit = SINE_LUT[(timeIdxB + colorPhaseB[i]) & LUT_MASK] > 0 ? 1 : 0;
                        const colorIdx = (rBit << 2) | (gBit << 1) | bBit;
                        targetFillStyle = (renderState.colorMode !== false && colorIdx !== 0) ? COLOR_LUT[colorIdx - 1] : COLOR_MAIN;
                    }
                }
                if (lastFillStyle !== targetFillStyle) {
                    ctx.fillStyle = targetFillStyle;
                    lastFillStyle = targetFillStyle;
                }
                const baseSquareSize = Math.max(2.0, (seedPx * (prio === 199 ? 0.75 : 0.5)) | 0);
                const finalSize = (baseSquareSize * atomicScale * renderScale) | 0;
                const halfSize = finalSize * 0.5;
                if (renderState.invertCanvas) ctx.fillStyle = 'rgb(255, 255, 255)';
                ctx.fillRect((drawX - halfSize) | 0, (drawY - halfSize) | 0, finalSize, finalSize);
            } else {
                const finalSize = Math.max(1.0, (targetSize * Math.min(op, 1.0) * atomicScale * renderScale) | 0);
                if (renderState.invertCanvas) {
                    if (lastGlobalAlpha !== 1.0) {
                        ctx.globalAlpha = 1.0;
                        lastGlobalAlpha = 1.0;
                    }
                }
                ctx.drawImage(atlasBitmap, au, av, aw, ah, (drawX - finalSize * 0.5) | 0, (drawY - finalSize * 0.5) | 0, finalSize, finalSize);
            }
            isAnimating = true;
        }
    }

    ctx.globalCompositeOperation = 'source-over';
    ctx.globalAlpha = 1.0;
    const needsRender = isAnimating || smoothedIntensity > 0.01 || renderState.appState === 'RESIZE';
    if (needsRender) {
        requestAnimationFrame(loop);
    } else {
        isLoopRunning = false;
    }
}

