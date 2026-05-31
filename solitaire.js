/*
 * Copyright 2026 Akop Karapetyan
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

'use strict';

// --- Constants ---

const LOGICAL_W = 640;    // logical canvas width (fixed; canvas scales to match)
const CARD_W    = 71;     // sprite tile width  (px)
const CARD_H    = 96;     // sprite tile height (px)
const IX_EMPTY_SLOT = 77; // sprite index of the empty card slot
const IX_WASTE_RECY = 75; // sprite index of the recyclable waste slot
const IX_WASTE_DONE = 76; // sprite index of the finished waste slot
const IX_BACKS = [
    [52],[53],[54],[55],[56],[57], // Available card-back sprite indices
    [58,59,60],                    // Some are animated, so additional indices
    [61],[62],                     // represent additional frames
    [63,64],
    [65,66,67],
    [68,69,70],
];
const SS_CARDS_PER_ROW = 13; // cards per row in the sprite sheet
const DC_CARDS_PER_ROW = 6;  // deck chooser cards per row
const DC_CARD_PADDING = 4;   // deck chooser card padding

const SPRITE_URL = 'cards.png';

// Suit → sprite row mapping
const SUIT_ROW = { S: 0, H: 1, C: 2, D: 3 };
const SUITS    = ['S', 'H', 'C', 'D'];
const RED_SUITS = new Set(['H', 'D']);

// Base layout positions in logical coordinates (640 wide)
const L = {
    STOCK_X: 17,
    STOCK_Y: 5,
    THICK_X_OFFSET: 2, // h. offset between cards added for thickness effect
    THICK_Y_OFFSET: 1, // v. offset between cards added for thickness effect
    WASTE_X: 105,
    WASTE_Y: 5,
    FOUND_X: [281, 369, 457, 545],
    FOUND_Y: 5,
    TAB_X:   [17, 105, 193, 281, 369, 457, 545],
    TAB_Y:   107,
    FD_DY:   3,    // face-down card vertical offset
    FU_DY:   20,   // face-up card offset (base; auto-compressed for tall piles)
    WASTE3_DX: 14, // horizontal fan offset in Draw-3 mode
    WASTE3_DY: 1,  // vertical fan offset in Draw-3 mode
};

// Standard-scoring point deltas
const SCORE = {
    WASTE_TO_FOUND: 10,
    WASTE_TO_TAB:    5,
    TAB_FLIP:        5,
    FOUND_TO_TAB:  -15,
    RECYCLE:      -100,
};

// --- Card Utilities ---

function makeCard(suit, rank) {
    return { suit, rank, faceUp: false };
}

function cloneCard(c) {
    return { suit: c.suit, rank: c.rank, faceUp: c.faceUp };
}

function cardIsRed(c) {
    return RED_SUITS.has(c.suit);
}

function rankLabel(rank) {
    const face = { 1: 'A', 11: 'J', 12: 'Q', 13: 'K' };
    return face[rank] ?? String(rank);
}

function suitSymbol(suit) {
    const syms = { S: '\u2660', H: '\u2665', C: '\u2663', D: '\u2666' };
    return syms[suit];
}

// --- State ---

const canvas = document.getElementById('board');
const ctx    = canvas.getContext('2d');

let spriteSheet = null;
let spriteReady = false;    // true once the sprite image has loaded

let pendingBack  = 9;       // staged value while deck dialog is open

const options = {
    timed: true,
    statusBar: true,
    outlineDrag: false,
    drawCount: 3,
    scoring: 'standard',
    deck: 9,
};

let state     = null;       // full game state object (see freshState)
let undoState = null;       // one-level undo snapshot

let drag = null;            // active drag descriptor or null

// Win animation
let winParticles = [];
let winAnimating = false;
let winAnimFrame = null;
let winAbortFn   = null;    // called to stop the win animation early

// Timer
let timerInterval = null;

// Double-tap detection (mobile)
let lastTapTime = 0;
let lastTapX    = 0;
let lastTapY    = 0;

// Active dropdown menu
let activeMenu = null;

// --- Deck & Deal ---

function freshState() {
    return {
        stock:           [],
        waste:           [],
        foundations:     [[], [], [], []],   // indexed 0-3, one per suit slot
        tableau:         [[], [], [], [], [], [], []],
        drawCount:       options.drawCount,
        scoring:         options.scoring,
        score:           options.scoring === 'vegas' ? -52 : 0,
        elapsed:         0,
        passes:          0,
        won:             false,
        autoCompleting:  false,
    };
}

function makeDeck() {
    const deck = [];
    for (const suit of SUITS) {
        for (let rank = 1; rank <= 13; rank++) {
            deck.push(makeCard(suit, rank));
        }
    }
    return deck;
}

function shuffle(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [arr[i], arr[j]] = [arr[j], arr[i]];
    }
}

function deal() {
    const s = freshState();
    const deck = makeDeck();
    shuffle(deck);

    // Deal tableau: column i gets i+1 cards, top card face-up
    let di = 0;
    for (let col = 0; col < 7; col++) {
        for (let row = 0; row <= col; row++) {
            const card = deck[di++];
            card.faceUp = (row === col);
            s.tableau[col].push(card);
        }
    }

    // Remaining cards go to stock, face-down
    while (di < deck.length) {
        deck[di].faceUp = false;
        s.stock.push(deck[di++]);
    }

    return s;
}

function deepClone(s) {
    return {
        stock:          s.stock.map(cloneCard),
        waste:          s.waste.map(cloneCard),
        foundations:    s.foundations.map(f => f.map(cloneCard)),
        tableau:        s.tableau.map(col => col.map(cloneCard)),
        drawCount:      s.drawCount,
        scoring:        s.scoring,
        score:          s.score,
        elapsed:        s.elapsed,
        passes:         s.passes,
        won:            s.won,
        autoCompleting: s.autoCompleting,
    };
}

// --- Move Validation ---

function canDropOnTableau(card, colIdx) {
    const col = state.tableau[colIdx];
    if (col.length === 0) {
        return card.rank === 13;   // only Kings on empty
    }
    const top = col[col.length - 1];
    return top.faceUp &&
           cardIsRed(card) !== cardIsRed(top) &&
           card.rank === top.rank - 1;
}

function canDropOnFoundation(card, fi) {
    const found = state.foundations[fi];
    if (found.length === 0) {
        return card.rank === 1;  // Ace starts
    }
    const top = found[found.length - 1];
    return card.suit === top.suit && card.rank === top.rank + 1;
}

// Return the index of the best foundation that will accept card, or -1
function findBestFoundation(card) {
    for (let i = 0; i < 4; i++) {
        if (canDropOnFoundation(card, i)) {
            return i;
        }
    }
    return -1;
}

// --- Scoring ---

function addScore(event) {
    if (state.scoring !== 'standard') return;
    const delta = SCORE[event] ?? 0;
    state.score = Math.max(0, state.score + delta);
    updateStatusBar();
}

function addVegasScore(delta) {
    if (state.scoring !== 'vegas') return;
    state.score += delta;
    updateStatusBar();
}

function computeWinBonus() {
    if (state.scoring === 'standard' && options.timed && state.elapsed > 0) {
        state.score += Math.floor(700000 / state.elapsed);
        updateStatusBar();
    }
}

// --- Layout Helpers ---

// Pixels-per-logical-pixel for the current canvas size
function getScale() {
    const dpr = window.devicePixelRatio || 1;
    return (canvas.width / dpr) / LOGICAL_W;
}

// Logical height of the canvas
function logicalH() {
    const dpr = window.devicePixelRatio || 1;
    return canvas.height / dpr / getScale();
}

// Compute the dynamic face-up reveal offset for a tableau column.
// Compresses the pile if it would otherwise overflow the canvas.
function faceUpDy(colIdx) {
    const pile    = state.tableau[colIdx];
    const fdCount = pile.filter(c => !c.faceUp).length;
    const fuCount = pile.filter(c => c.faceUp).length;
    const avail   = logicalH() - L.TAB_Y - CARD_H - 8;
    let dy = L.FU_DY;
    if (fuCount > 1 && fdCount * L.FD_DY + fuCount * dy > avail) {
        dy = Math.max(10, Math.floor((avail - fdCount * L.FD_DY) / fuCount));
    }
    return dy;
}

// --- Rendering ---

function resizeCanvas() {
    const dpr = window.devicePixelRatio || 1;
    canvas.width  = Math.round(canvas.clientWidth  * dpr);
    canvas.height = Math.round(canvas.clientHeight * dpr);
    render();
}

function render() {
    if (!state) return;

    const dpr   = window.devicePixelRatio || 1;
    const scale = getScale();
    const lh    = logicalH();

    ctx.save();
    ctx.scale(scale * dpr, scale * dpr);

    // Green felt background
    ctx.fillStyle = '#008000';
    ctx.fillRect(0, 0, LOGICAL_W, lh);

    drawBoard(lh);

    if (winParticles.length > 0) {
        drawWinParticles();
    } else if (state.won && !winAnimating) {
        drawWinOverlay(lh);
    }

    if (drag) drawDragStack();

    ctx.restore();
}

function drawBoard(lh) {
    drawStock();
    drawWaste();
    drawFoundations();
    drawTableau(lh);
}

function drawStock() {
    if (state.stock.length > 0) {
        const cardCount = Math.trunc((state.stock.length - 1) / 8) + 1;
        for (let i = 0; i < cardCount; i++) {
            drawBack(
                L.STOCK_X + i * L.THICK_X_OFFSET,
                L.STOCK_Y + i * L.THICK_Y_OFFSET
            );
        }
    } else {
        const canRecycle = !(state.scoring === 'vegas' && state.drawCount === 3 && state.passes >= 1);
        drawWasteSlot(L.STOCK_X, L.STOCK_Y, canRecycle);
    }
}

function drawWaste() {
    const wasteLen  = state.waste.length;
    const isDragged = drag && drag.src.type === 'waste';

    if (wasteLen === 0) {
        return;
    }

    // We draw some cards for thickness effect, depending on the number
    // left in the waste. Doesn't really matter what we draw - it'll be covered
    const effectCardCount = (state.drawCount === 1)
        ? Math.max(0, Math.trunc((wasteLen - 2) / 10))
        : Math.max(0, Math.trunc((wasteLen - 3) / 10));
    let offsetX = L.WASTE_X;
    let offsetY = L.WASTE_Y;
    for (let i = 0; i < effectCardCount; i++) {
        drawCard(
            state.waste[0],
            offsetX,
            offsetY
        );
        offsetX += L.THICK_X_OFFSET;
        offsetY += L.THICK_Y_OFFSET;
    }

    if (state.drawCount === 1) {
        if (!isDragged) {
            drawCard(state.waste[wasteLen - 1], offsetX, offsetY);
        }
        return;
    }

    // Draw-3: fan of up to 3 cards; only top card is playable
    const count  = Math.min(3, wasteLen);
    const start  = wasteLen - count;
    const topIdx = wasteLen - 1;

    for (let i = 0; i < count; i++) {
        const cardIdx = start + i;
        if (isDragged && cardIdx === topIdx) {
            continue;
        }
        drawCard(
            state.waste[cardIdx],
            offsetX,
            offsetY
        );
        offsetX += L.WASTE3_DX;
        offsetY += L.WASTE3_DY;
    }
}

function drawFoundations() {
    for (let fi = 0; fi < 4; fi++) {
        const x         = L.FOUND_X[fi];
        const y         = L.FOUND_Y;
        const pile      = state.foundations[fi];
        const isDragged = drag && drag.src.type === 'foundation' && drag.src.fi === fi;
        const visLen    = pile.length - (isDragged ? 1 : 0);

        if (visLen <= 0) {
            drawSlot(x, y);
        } else {
            drawCard(pile[visLen - 1], x, y);
        }
    }
}

function drawTableau(lh) {
    for (let col = 0; col < 7; col++) {
        const pile = state.tableau[col];
        const cx   = L.TAB_X[col];

        if (pile.length === 0) {
            continue;
        }

        const isDragSrc = drag && drag.src.type === 'tableau' && drag.src.col === col;
        const cutIdx    = isDragSrc ? drag.src.idx : pile.length;
        const dy        = faceUpDy(col);
        let y           = L.TAB_Y;

        for (let j = 0; j < cutIdx; j++) {
            const card = pile[j];
            card.faceUp ? drawCard(card, cx, y) : drawBack(cx, y);
            if (j < cutIdx - 1) y += pile[j].faceUp ? dy : L.FD_DY;
        }
    }
}

// Draw a face-up card using the sprite sheet (or vector fallback)
function drawCard(card, x, y) {
    if (spriteReady) {
        const sx = (card.rank - 1) * CARD_W;
        const sy = SUIT_ROW[card.suit] * CARD_H;
        ctx.drawImage(spriteSheet, sx, sy, CARD_W, CARD_H, x, y, CARD_W, CARD_H);
    } else {
        drawCardFallback(card, x, y);
    }
}

// Draw a face-down card back
function drawBack(x, y) {
    if (spriteReady) {
        const spriteIndex = IX_BACKS[options.deck][0];
        const sx = (spriteIndex * CARD_W) % spriteSheet.width;
        const sy = Math.trunc(spriteIndex / SS_CARDS_PER_ROW) * CARD_H;
        ctx.drawImage(spriteSheet, sx, sy, CARD_W, CARD_H, x, y, CARD_W, CARD_H);
    } else {
        drawBackFallback(x, y);
    }
}

// Draw an empty card-slot outline; showArrow draws a recycle icon
function drawSlot(x, y) {
    ctx.save();
    if (spriteReady) {
        const sx = (IX_EMPTY_SLOT * CARD_W) % spriteSheet.width;
        const sy = Math.trunc(IX_EMPTY_SLOT / SS_CARDS_PER_ROW) * CARD_H;
        ctx.drawImage(spriteSheet, sx, sy, CARD_W, CARD_H, x, y, CARD_W, CARD_H);
    } else {
        ctx.strokeStyle = '#004400';
        ctx.lineWidth   = 1;
        ctx.setLineDash([4, 4]);
        roundRect(x, y, CARD_W, CARD_H, 4);
        ctx.stroke();
        ctx.setLineDash([]);
    }
    ctx.restore();
}

function drawWasteSlot(x, y, canRecycle) {
    ctx.save();
    if (spriteReady) {
        const spriteIndex = canRecycle ? IX_WASTE_RECY : IX_WASTE_DONE;
        const sx = (spriteIndex * CARD_W) % spriteSheet.width;
        const sy = Math.trunc(spriteIndex / SS_CARDS_PER_ROW) * CARD_H;
        ctx.drawImage(spriteSheet, sx, sy, CARD_W, CARD_H, x, y, CARD_W, CARD_H);
    } else {
        ctx.strokeStyle = '#004400';
        ctx.lineWidth   = 1;
        ctx.setLineDash([4, 4]);
        roundRect(x, y, CARD_W, CARD_H, 4);
        ctx.stroke();
        ctx.setLineDash([]);
        if (canRecycle) {
            const cx = x + CARD_W / 2;
            const cy = y + CARD_H / 2;
            ctx.strokeStyle = '#006600';
            ctx.lineWidth   = 2;
            // Circle arc
            ctx.beginPath();
            ctx.arc(cx, cy, 14, -Math.PI * 0.85, Math.PI * 0.85);
            ctx.stroke();
            // Arrow tip at the open end
            const angle = Math.PI * 0.85;
            const ax = cx + 14 * Math.cos(angle);
            const ay = cy + 14 * Math.sin(angle);
            ctx.beginPath();
            ctx.moveTo(ax - 5, ay - 2);
            ctx.lineTo(ax,     ay + 4);
            ctx.lineTo(ax + 5, ay - 2);
            ctx.stroke();
        }
    }
    ctx.restore();
}

// Vector fallback card face (used when sprite sheet has not yet loaded)
function drawCardFallback(card, x, y) {
    const isRed = cardIsRed(card);
    const color = isRed ? '#cc0000' : '#000000';

    ctx.fillStyle = '#ffffff';
    roundRect(x, y, CARD_W, CARD_H, 4);
    ctx.fill();
    ctx.strokeStyle = '#aaaaaa';
    ctx.lineWidth   = 1;
    ctx.stroke();

    const rl  = rankLabel(card.rank);
    const sym = suitSymbol(card.suit);

    ctx.fillStyle    = color;
    ctx.font         = 'bold 11px Arial';
    ctx.textBaseline = 'top';
    ctx.textAlign    = 'left';
    ctx.fillText(rl,  x + 3, y + 2);
    ctx.fillText(sym, x + 3, y + 15);

    // Bottom-right corner (rotated 180°)
    ctx.save();
    ctx.translate(x + CARD_W - 3, y + CARD_H - 2);
    ctx.rotate(Math.PI);
    ctx.fillText(rl,  0, 0);
    ctx.fillText(sym, 0, 13);
    ctx.restore();

    // Centre suit symbol
    ctx.font         = '26px Arial';
    ctx.textAlign    = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText(sym, x + CARD_W / 2, y + CARD_H / 2);

    ctx.textAlign    = 'left';
    ctx.textBaseline = 'alphabetic';
}

// Vector fallback card back
function drawBackFallback(x, y) {
    ctx.fillStyle = '#000080';
    roundRect(x, y, CARD_W, CARD_H, 4);
    ctx.fill();
    ctx.strokeStyle = '#ffffff';
    ctx.lineWidth   = 2;
    ctx.stroke();
    // Simple vertical stripe pattern
    ctx.strokeStyle = '#3333aa';
    ctx.lineWidth   = 1;
    for (let i = 8; i < CARD_W - 4; i += 8) {
        ctx.beginPath();
        ctx.moveTo(x + i, y + 5);
        ctx.lineTo(x + i, y + CARD_H - 5);
        ctx.stroke();
    }
}

// Draw the currently-dragged card stack at its current position
function drawDragStack() {
    const cards = drag.cards;

    if (options.outlineDrag && !drag.isTouch) {
        ctx.strokeStyle = 'rgba(0,0,0,0.7)';
        ctx.lineWidth   = 2;
        ctx.setLineDash([4, 4]);
        for (let i = 0; i < cards.length; i++) {
            roundRect(drag.x, drag.y + i * L.FU_DY, CARD_W, CARD_H, 4);
            ctx.stroke();
        }
        ctx.setLineDash([]);
    } else {
        ctx.save();
        if (drag.isTouch) {
            // Subtle scale-up on touch for finger-clearance feedback
            const sc = 1.06;
            const ox = (CARD_W * (sc - 1)) / 2;
            const oy = (CARD_H * (sc - 1)) / 2;
            ctx.translate(drag.x - ox, drag.y - oy);
            ctx.scale(sc, sc);
        } else {
            ctx.translate(drag.x, drag.y);
        }
        for (let i = 0; i < cards.length; i++) {
            drawCard(cards[i], 0, i * L.FU_DY);
        }
        ctx.restore();
    }
}

function drawWinParticles() {
    for (const p of winParticles) {
        drawCard(p.card, p.x, p.y);
    }
}

// Full-screen win overlay shown after the animation finishes
function drawWinOverlay(lh) {
    ctx.fillStyle = 'rgba(0,0,0,0.45)';
    ctx.fillRect(0, 0, LOGICAL_W, lh);

    const cx = LOGICAL_W / 2;
    const cy = lh / 2;

    ctx.textAlign    = 'center';
    ctx.textBaseline = 'middle';

    ctx.fillStyle = '#ffffff';
    ctx.font      = 'bold 30px Arial';
    ctx.fillText('You Win!', cx, cy - 26);

    if (state.scoring !== 'none') {
        const label = state.scoring === 'vegas'
            ? `$${state.score}`
            : `Score: ${state.score}`;
        ctx.font = '16px Arial';
        ctx.fillText(label, cx, cy + 10);
    }

    ctx.fillStyle = '#cccccc';
    ctx.font      = '13px Arial';
    ctx.fillText('Click or tap to deal again', cx, cy + 40);

    ctx.textAlign    = 'left';
    ctx.textBaseline = 'alphabetic';
}

// Helper: build a rounded-rect path (no stroke/fill; caller does that)
function roundRect(x, y, w, h, r) {
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.lineTo(x + w - r, y);
    ctx.quadraticCurveTo(x + w, y,     x + w, y + r);
    ctx.lineTo(x + w, y + h - r);
    ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
    ctx.lineTo(x + r, y + h);
    ctx.quadraticCurveTo(x,     y + h, x,     y + h - r);
    ctx.lineTo(x, y + r);
    ctx.quadraticCurveTo(x,     y,     x + r, y);
    ctx.closePath();
}

// --- Drag & Drop ---

// Convert a DOM client position to logical (640-wide) canvas coordinates
function toLogical(clientX, clientY) {
    const rect = canvas.getBoundingClientRect();
    const scl  = LOGICAL_W / rect.width;
    return {
        x: (clientX - rect.left) * scl,
        y: (clientY - rect.top)  * scl,
    };
}

// Return the y-positions of each card in a tableau column
function tabCardYs(colIdx) {
    const pile = state.tableau[colIdx];
    const dy   = faceUpDy(colIdx);
    const ys   = [];
    let y      = L.TAB_Y;
    for (let j = 0; j < pile.length; j++) {
        ys.push(y);
        if (j < pile.length - 1) y += pile[j].faceUp ? dy : L.FD_DY;
    }
    return ys;
}

// Hit-test a logical point; returns a descriptor or null
function hitTest(lx, ly) {
    // Tableau columns (right-to-left so rightmost column takes priority)
    for (let col = 6; col >= 0; col--) {
        const pile = state.tableau[col];
        if (pile.length === 0) continue;
        const cx = L.TAB_X[col];
        if (lx < cx || lx > cx + CARD_W) continue;

        const ys = tabCardYs(col);
        for (let j = pile.length - 1; j >= 0; j--) {
            const top    = ys[j];
            const bottom = j < pile.length - 1 ? ys[j + 1] : top + CARD_H;
            if (ly >= top && ly <= bottom) {
                return { type: 'tableau', col, idx: j, cardX: cx, cardY: top };
            }
        }
    }

    // Waste pile top card
    if (state.waste.length > 0) {
        const count  = state.drawCount === 3 ? Math.min(3, state.waste.length) : 1;
        const topX   = L.WASTE_X + (count - 1) * L.WASTE3_DX;
        if (lx >= topX && lx <= topX + CARD_W &&
            ly >= L.WASTE_Y && ly <= L.WASTE_Y + CARD_H) {
            return { type: 'waste', cardX: topX, cardY: L.WASTE_Y };
        }
    }

    // Foundation piles
    for (let fi = 0; fi < 4; fi++) {
        const fx = L.FOUND_X[fi];
        if (lx >= fx && lx <= fx + CARD_W &&
            ly >= L.FOUND_Y && ly <= L.FOUND_Y + CARD_H) {
            return { type: 'foundation', fi, cardX: fx, cardY: L.FOUND_Y };
        }
    }

    // Stock pile
    if (lx >= L.STOCK_X && lx <= L.STOCK_X + CARD_W &&
        ly >= L.STOCK_Y && ly <= L.STOCK_Y + CARD_H) {
        return { type: 'stock' };
    }

    return null;
}

function onPointerDown(lx, ly, isTouch) {
    // Clicking anywhere on the win overlay starts a new game
    if (state.won && !winAnimating) {
        startNewGame();
        return;
    }
    if (state.won || state.autoCompleting || drag) return;

    const hit = hitTest(lx, ly);
    if (!hit) return;

    if (hit.type === 'stock') {
        undoState = deepClone(state);
        doDrawStock();
        render();
        return;
    }

    let cards = [];
    let src   = null;

    if (hit.type === 'waste') {
        const top = state.waste[state.waste.length - 1];
        if (!top || !top.faceUp) return;
        cards = [cloneCard(top)];
        src   = { type: 'waste' };

    } else if (hit.type === 'tableau') {
        const pile = state.tableau[hit.col];
        const card = pile[hit.idx];
        if (!card || !card.faceUp) return;
        cards = pile.slice(hit.idx).map(cloneCard);
        src   = { type: 'tableau', col: hit.col, idx: hit.idx };

    } else if (hit.type === 'foundation') {
        const found = state.foundations[hit.fi];
        if (found.length === 0) return;
        cards = [cloneCard(found[found.length - 1])];
        src   = { type: 'foundation', fi: hit.fi };

    } else {
        return;
    }

    undoState = deepClone(state);
    drag = {
        cards,
        src,
        x:       hit.cardX,
        y:       hit.cardY,
        ox:      lx - hit.cardX,
        oy:      ly - hit.cardY,
        isTouch,
    };
    render();
}

function onPointerMove(lx, ly) {
    if (!drag) return;
    drag.x = lx - drag.ox;
    drag.y = ly - drag.oy;
    render();
}

function onPointerUp(lx, ly) {
    if (!drag) return;

    // Use the centre of the dragged card (not the raw pointer) for drop detection.
    // This makes it much easier to place cards accurately.
    const cx = drag.x + CARD_W / 2;
    const cy = drag.y + CARD_H / 2;
    const target = findDropTarget(cx, cy);
    const moved  = target ? commitMove(drag.src, drag.cards, target) : false;

    if (!moved) undoState = null;   // cancelled drag → discard undo snapshot

    drag = null;
    render();

    if (moved) {
        checkAutoComplete();
        checkWin();
    }
}

// Find a valid drop target for the current drag, or return null
function findDropTarget(lx, ly) {
    // Tableau columns
    for (let col = 0; col < 7; col++) {
        const cx   = L.TAB_X[col];
        const pile = state.tableau[col];

        // Target zone is the last visible card area (or the empty-column slot)
        let targetY = L.TAB_Y;
        if (pile.length > 0) {
            const dy = faceUpDy(col);
            for (let j = 0; j < pile.length - 1; j++) {
                targetY += pile[j].faceUp ? dy : L.FD_DY;
            }
        }

        // Generous hit zone: 16px slack above and below the target card
        if (lx >= cx && lx <= cx + CARD_W &&
            ly >= targetY - 16 && ly <= targetY + CARD_H + 8) {
            if (drag.src.type === 'tableau' && drag.src.col === col) continue;
            if (canDropOnTableau(drag.cards[0], col)) return { type: 'tableau', col };
        }
    }

    // Foundation piles (single-card drops only)
    if (drag.cards.length === 1) {
        for (let fi = 0; fi < 4; fi++) {
            const fx = L.FOUND_X[fi];
            if (lx >= fx && lx <= fx + CARD_W &&
                ly >= L.FOUND_Y - 8 && ly <= L.FOUND_Y + CARD_H + 8) {
                if (canDropOnFoundation(drag.cards[0], fi)) return { type: 'foundation', fi };
            }
        }
    }

    return null;
}

// Apply a move to the game state and update scoring
function commitMove(src, cards, target) {
    // Remove cards from source pile
    if (src.type === 'waste') {
        state.waste.pop();

    } else if (src.type === 'tableau') {
        state.tableau[src.col].splice(src.idx);
        flipTopTableauCard(src.col);

    } else if (src.type === 'foundation') {
        state.foundations[src.fi].pop();
        addScore('FOUND_TO_TAB');
    }

    // Place cards on target pile
    if (target.type === 'tableau') {
        for (const c of cards) {
            c.faceUp = true;
            state.tableau[target.col].push(c);
        }
        if (src.type === 'waste') addScore('WASTE_TO_TAB');

    } else if (target.type === 'foundation') {
        const c = cards[0];
        c.faceUp = true;
        state.foundations[target.fi].push(c);
        if (src.type === 'waste') addScore('WASTE_TO_FOUND');
        addVegasScore(5);
    }

    saveState();

    return true;
}

function saveState() {
    const s = serialize(state);
    if (s) {
        window.history.replaceState(null, '', `#${s}`);
    } else {
        window.history.replaceState(null, '', ' ');
    }
}

function saveOptions(opts) {
    const optString = JSON.stringify(opts);

    const date = new Date();
    date.setTime(date.getTime() + (365 * 24 * 60 * 60 * 1000)); // 1 year

    document.cookie = `options=${encodeURIComponent(optString)}; expires=${date.toUTCString()}; path=/; SameSite=Strict; Secure`;
}

function loadOptions() {
    const optionsCookie = document.cookie.split('; ').find(row => row.startsWith('options='));
    if (optionsCookie) {
        const optString = decodeURIComponent(optionsCookie.split('=')[1]);
        if (optString) {
            return JSON.parse(optString);
        }
    }
    return null;
}

// Turn over the top face-down card in a tableau column after cards are removed
function flipTopTableauCard(col) {
    const pile = state.tableau[col];
    if (pile.length > 0 && !pile[pile.length - 1].faceUp) {
        pile[pile.length - 1].faceUp = true;
        addScore('TAB_FLIP');
    }
}

// Double-click / double-tap: auto-move the top card of src to a foundation
function autoMoveToFoundation(src) {
    let card = null;
    if (src.type === 'waste') {
        if (state.waste.length === 0) {
            return false;
        }
        card = state.waste[state.waste.length - 1];
    } else if (src.type === 'tableau') {
        const pile = state.tableau[src.col];
        if (pile.length === 0) {
            return false;
        }
        src.idx = pile.length - 1;  // ensure we're trying to move the top card
        card = pile[src.idx];
        if (!card.faceUp) {
            return false;
        }
    }

    if (!card) {
        return false;
    }

    const fi = findBestFoundation(card);
    if (fi === -1) {
        return false;
    }

    undoState = deepClone(state);
    commitMove(src, [cloneCard(card)], { type: 'foundation', fi });
    render();
    checkAutoComplete();
    checkWin();

    return true;
}

// --- Stock & Waste ---

function doDrawStock() {
    if (state.stock.length === 0) {
        recycleWaste();
        return;
    }
    const count = Math.min(state.drawCount, state.stock.length);
    for (let i = 0; i < count; i++) {
        const card = state.stock.pop();
        card.faceUp = true;
        state.waste.push(card);
    }
}

function recycleWaste() {
    // Vegas Draw-3: only one pass through the deck, no recycle
    if (state.scoring === 'vegas' && state.drawCount === 3) return;

    state.passes++;
    // Draw-1 Standard: second and subsequent recycles cost -100
    if (state.scoring === 'standard' && state.drawCount === 1 && state.passes > 1) {
        addScore('RECYCLE');
    }

    while (state.waste.length > 0) {
        const card = state.waste.pop();
        card.faceUp = false;
        state.stock.push(card);
    }
}

// --- Auto-complete & Win Detection ---

// True when stock + waste are empty and every tableau card is face-up
function allFaceUp() {
    if (state.stock.length > 0 || state.waste.length > 0) return false;
    for (const col of state.tableau) {
        for (const c of col) {
            if (!c.faceUp) return false;
        }
    }
    return true;
}

function checkAutoComplete() {
    if (state.autoCompleting || state.won) return;
    if (!allFaceUp()) return;
    state.autoCompleting = true;
    scheduleAutoStep();
}

function scheduleAutoStep() {
    setTimeout(runAutoStep, 50);
}

// Move one card per tick from tableau to foundation, then reschedule
function runAutoStep() {
    if (!state.autoCompleting) return;

    let moved = false;
    for (let col = 0; col < 7 && !moved; col++) {
        const pile = state.tableau[col];
        if (pile.length === 0) continue;
        const card = pile[pile.length - 1];
        const fi   = findBestFoundation(card);
        if (fi !== -1) {
            pile.pop();
            state.foundations[fi].push(card);
            addVegasScore(5);
            moved = true;
        }
    }

    if (moved) {
        render();
        if (checkWin()) return;
        scheduleAutoStep();
    } else {
        state.autoCompleting = false;
    }
}

// Returns true if the game is now won; triggers animation
function checkWin() {
    if (state.won) return true;
    const total = state.foundations.reduce((sum, f) => sum + f.length, 0);
    if (total < 52) return false;

    state.won          = true;
    state.autoCompleting = false;
    stopTimer();
    computeWinBonus();
    startWinAnimation();
    return true;
}

// --- Win Animation (bouncing cards) ---

class Particle {
    constructor(card, x, y) {
        this.card    = card;
        this.x       = x;
        this.y       = y;
        this.vx      = (Math.random() - 0.5) * 11;
        this.vy      = -(Math.random() * 10 + 5);
        this.bounces = 0;
    }

    update(lh) {
        this.x  += this.vx;
        this.y  += this.vy;
        this.vy += 0.45;   // gravity

        if (this.y + CARD_H >= lh) {
            this.y  = lh - CARD_H;
            this.vy = -(Math.abs(this.vy) * 0.72);
            this.bounces++;
        }
    }

    isDone() {
        return this.x > LOGICAL_W || this.x < -CARD_W || this.bounces > 5;
    }
}

function startWinAnimation() {
    // Cancel any previous win animation
    if (winAbortFn) { winAbortFn(); winAbortFn = null; }
    if (winAnimFrame) { cancelAnimationFrame(winAnimFrame); winAnimFrame = null; }

    winParticles = [];
    winAnimating = true;
    let aborted  = false;

    // Build a list of deck indices and shuffle them
    const foundationDecks = [];
    for (let fi = 0; fi < 4; fi++) {
        foundationDecks.push(fi, fi, fi, fi, fi, fi, fi, fi, fi, fi, fi, fi, fi);
    }
    shuffle(foundationDecks);

    function launchNext() {
        if (aborted || !foundationDecks.length) {
            return;
        }
        const fi = foundationDecks.pop();
        const card = state.foundations[fi].pop();
        winParticles.push(new Particle(card, L.FOUND_X[fi], L.FOUND_Y));
        if (foundationDecks.length) {
            setTimeout(launchNext, 65);
        }
    }
    launchNext();

    function animLoop() {
        if (aborted) {
            return;
        }
        const lh = logicalH();
        for (const p of winParticles) {
            p.update(lh);
        }
        winParticles = winParticles.filter(p => !p.isDone());
        render();

        if (winParticles.length > 0 || foundationDecks.length) {
            winAnimFrame = requestAnimationFrame(animLoop);
        } else {
            winAnimating = false;
            render();   // show the "You Win!" overlay
        }
    }
    winAnimFrame = requestAnimationFrame(animLoop);

    winAbortFn = () => {
        aborted = true;
        for (let fi = 0; fi < 4; fi++) {
            state.foundations[fi] = [];
        }
    };
}

// --- Timer ---

function startTimer() {
    stopTimer();
    if (!options.timed || state.scoring === 'none') {
        return;
    }
    timerInterval = setInterval(tickTimer, 1000);
}

function stopTimer() {
    if (timerInterval) {
        clearInterval(timerInterval);
        timerInterval = null;
    }
}

function tickTimer() {
    state.elapsed++;
    // Standard timed penalty: -2 pts every 10 seconds
    if (state.scoring === 'standard' && state.elapsed % 10 === 0) {
        state.score = Math.max(0, state.score - 2);
    }
    updateStatusBar();
}

function updateStatusBar() {
    const scoreEl = document.getElementById('st-score');
    const timeEl  = document.getElementById('st-time');

    if (!options.statusBar) {
        scoreEl.textContent = '';
        timeEl.textContent  = '';
        return;
    }

    if (state.scoring === 'vegas') {
        scoreEl.textContent = `$${state.score}`;
    } else if (state.scoring === 'standard') {
        scoreEl.textContent = `Score: ${state.score}`;
    } else {
        scoreEl.textContent = '';
    }

    timeEl.textContent = `Time: ${state.elapsed}`;
}

// --- Game Management ---

function startNewGame() {
    // Clean up any running win animation
    if (winAbortFn)   { winAbortFn(); winAbortFn = null; }
    if (winAnimFrame) { cancelAnimationFrame(winAnimFrame); winAnimFrame = null; }
    winParticles = [];
    winAnimating = false;

    stopTimer();
    undoState = null;
    drag      = null;
    state     = deal();

    saveState();
    startTimer();
    updateStatusBar();
    render();
}

function undo() {
    if (!undoState) return;
    state     = undoState;
    undoState = null;
    render();
    updateStatusBar();
}

// --- Menu System ---

function openMenu(menuId, btnEl) {
    closeMenu();
    const dd   = document.getElementById(menuId);
    const rect = btnEl.getBoundingClientRect();
    dd.style.left = rect.left + 'px';
    dd.style.top  = rect.bottom + 'px';
    dd.hidden     = false;
    btnEl.classList.add('active');
    activeMenu = { dd, btn: btnEl };

    // Close on next outside click
    setTimeout(() => document.addEventListener('click', onOutsideClick, { once: true }), 0);
}

function closeMenu() {
    if (!activeMenu) return;
    activeMenu.dd.hidden = true;
    activeMenu.btn.classList.remove('active');
    activeMenu = null;
}

function onOutsideClick(e) {
    if (activeMenu && !activeMenu.dd.contains(e.target)) closeMenu();
}

function handleMenuAction(action) {
    closeMenu();
    switch (action) {
        case 'deal':    startNewGame();      break;
        case 'undo':    undo();              break;
        case 'deck':    showDeckDialog();    break;
        case 'options': showOptionsDialog(); break;
        case 'exit':    window.close();      break;
        case 'about':   showAboutDialog();   break;
    }
}

// --- Dialogs ---

function showOverlay() {
    document.getElementById('overlay').hidden = false;
}

function hideOverlay() {
    document.getElementById('overlay').hidden = true;
}

function showOptionsDialog() {
    // Populate with current settings
    const drawRadio    = document.querySelector(`input[name="draw"][value="${options.drawCount}"]`);
    const scoringRadio = document.querySelector(`input[name="scoring"][value="${options.scoring}"]`);
    if (drawRadio)    drawRadio.checked    = true;
    if (scoringRadio) scoringRadio.checked = true;
    document.getElementById('opt-timed').checked     = options.timed;
    document.getElementById('opt-statusbar').checked = options.statusBar;
    document.getElementById('opt-outline').checked   = options.outlineDrag;

    showOverlay();
    document.getElementById('dlg-options').hidden = false;
}

function hideOptionsDialog(apply) {
    if (apply) {
        options.drawCount = parseInt(document.querySelector('input[name="draw"]:checked').value, 10);
        options.scoring   = document.querySelector('input[name="scoring"]:checked').value;
        options.timed      = document.getElementById('opt-timed').checked;
        options.statusBar  = document.getElementById('opt-statusbar').checked;
        options.outlineDrag = document.getElementById('opt-outline').checked;
        saveOptions(options);
        startNewGame();
    }
    hideOverlay();
    document.getElementById('dlg-options').hidden = true;
}

function showDeckDialog() {
    pendingBack = options.deck;
    showOverlay();
    document.getElementById('dlg-deck').hidden = false;
    renderDeckChooser();
}

function hideDeckDialog(apply) {
    if (apply) {
        options.deck = pendingBack;
        saveOptions(options);
        render();
    }
    hideOverlay();
    document.getElementById('dlg-deck').hidden = true;
}

// Render the card-back grid inside the deck-chooser canvas
function renderDeckChooser() {
    const dc    = document.getElementById('deck-chooser');
    const dctx  = dc.getContext('2d');
    const rows  = Math.ceil(IX_BACKS.length / DC_CARDS_PER_ROW);
    const cell  = CARD_W + DC_CARD_PADDING;

    dc.width  = DC_CARDS_PER_ROW * cell + DC_CARD_PADDING;
    dc.height = rows * (CARD_H + DC_CARD_PADDING) + DC_CARD_PADDING;

    dctx.fillStyle = '#c0c0c0';
    dctx.fillRect(0, 0, dc.width, dc.height);

    for (let i = 0; i < IX_BACKS.length; i++) {
        const col  = i % DC_CARDS_PER_ROW;
        const row  = Math.floor(i / DC_CARDS_PER_ROW);
        const x    = DC_CARD_PADDING + col * cell;
        const y    = DC_CARD_PADDING + row * (CARD_H + DC_CARD_PADDING);
        const spriteIndex = IX_BACKS[i][0];

        if (spriteReady) {
            dctx.drawImage(
                spriteSheet,
                (spriteIndex * CARD_W) % spriteSheet.width,
                Math.trunc(spriteIndex / SS_CARDS_PER_ROW) * CARD_H,
                CARD_W,
                CARD_H,
                x,
                y,
                CARD_W,
                CARD_H
            );
        } else {
            dctx.fillStyle = '#000080';
            dctx.fillRect(x, y, CARD_W, CARD_H);
        }

        if (pendingBack === i) {
            dctx.strokeStyle = '#ffff00';
            dctx.lineWidth   = 3;
            dctx.strokeRect(x - 1, y - 1, CARD_W + 2, CARD_H + 2);
        }
    }
}

function showAboutDialog() {
    showOverlay();
    document.getElementById('dlg-about').hidden = false;
}

function hideAboutDialog() {
    hideOverlay();
    document.getElementById('dlg-about').hidden = true;
}

// --- Event Wiring ---

function init() {
    const savedOptions = loadOptions();
    if (savedOptions) {
        if (savedOptions.drawCount in [1, 3]) {
            options.drawCount = savedOptions.drawCount;
        }
        if (savedOptions.scoring in ['standard', 'vegas', 'none']) {
            options.scoring = savedOptions.scoring;
        }
        options.timed = savedOptions.timed === true;
        options.statusBar = savedOptions.statusBar === true;
        options.outlineDrag = savedOptions.outlineDrag === true;
        if (savedOptions.deck >= 0 && savedOptions.deck < IX_BACKS.length) {
            options.deck = savedOptions.deck;
        }
    }

    // ── Sprite sheet ───────────────────────────────────────────
    spriteSheet = new Image();
    spriteSheet.onload = () => {
        spriteReady = true;
        render();
        renderDeckChooser();
    };
    spriteSheet.onerror = () => {
        console.warn('Sprite sheet failed to load; using vector card fallback.');
        spriteReady = false;
        render();
    };
    // No crossOrigin: drawImage works without CORS; canvas tainting is acceptable
    // since we never call getImageData / toDataURL.
    spriteSheet.src = SPRITE_URL;

    // ── Initial deal ──────────────────────────────────────────
    resizeCanvas();
    state = null;
    const savedState = window.location.hash.slice(1);
    if (savedState && savedState.length > 0) {
        state = deserialize(savedState);
    }
    if (!state) {
        state = deal();
    }
    startTimer();
    updateStatusBar();
    render();

    // ── Window resize ─────────────────────────────────────────
    window.addEventListener('resize', () => {
        resizeCanvas();
    });

    // ── Keyboard ──────────────────────────────────────────────
    document.addEventListener('keydown', (e) => {
        if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') {
            e.preventDefault();
            undo();
        }
    });

    // ── Menu bar buttons ──────────────────────────────────────
    document.getElementById('mb-game').addEventListener('click', (e) => {
        e.stopPropagation();
        if (activeMenu && activeMenu.dd.id === 'dd-game') { closeMenu(); return; }
        openMenu('dd-game', e.currentTarget);
    });

    document.getElementById('mb-help').addEventListener('click', (e) => {
        e.stopPropagation();
        if (activeMenu && activeMenu.dd.id === 'dd-help') { closeMenu(); return; }
        openMenu('dd-help', e.currentTarget);
    });

    // Dropdown item clicks
    document.querySelectorAll('.dd-item').forEach((item) => {
        item.addEventListener('click', () => handleMenuAction(item.dataset.act));
    });

    // ── Options dialog ────────────────────────────────────────
    document.getElementById('opts-ok').addEventListener('click',     () => hideOptionsDialog(true));
    document.getElementById('opts-cancel').addEventListener('click',  () => hideOptionsDialog(false));

    // ── Deck dialog ───────────────────────────────────────────
    document.getElementById('deck-ok').addEventListener('click',     () => hideDeckDialog(true));
    document.getElementById('deck-cancel').addEventListener('click',  () => hideDeckDialog(false));

    // Click on the chooser canvas to pick a back
    document.getElementById('deck-chooser').addEventListener('click', (e) => {
        const dc   = document.getElementById('deck-chooser');
        const rect = dc.getBoundingClientRect();
        const px   = (e.clientX - rect.left) * (dc.width  / rect.width);
        const py   = (e.clientY - rect.top)  * (dc.height / rect.height);
        const col  = Math.floor((px - DC_CARD_PADDING) / (CARD_W + DC_CARD_PADDING));
        const row  = Math.floor((py - DC_CARD_PADDING) / (CARD_H + DC_CARD_PADDING));
        const idx  = row * DC_CARDS_PER_ROW + col;
        if (idx >= 0 && idx < IX_BACKS.length) {
            pendingBack = idx;
            renderDeckChooser();
        }
    });

    // ── About dialog ──────────────────────────────────────────
    document.getElementById('about-ok').addEventListener('click', () => hideAboutDialog());

    // Generic dialog close buttons (✕ in title bar)
    document.querySelectorAll('.dlg-close').forEach((btn) => {
        btn.addEventListener('click', () => {
            const dlg = btn.closest('.dialog');
            if (!dlg) return;
            dlg.hidden = true;
            hideOverlay();
        });
    });

    // ── Canvas — mouse ────────────────────────────────────────
    canvas.addEventListener('mousedown', (e) => {
        if (e.button !== 0) return;
        if (activeMenu) { closeMenu(); return; }
        const lp = toLogical(e.clientX, e.clientY);
        onPointerDown(lp.x, lp.y, false);
    });

    canvas.addEventListener('mousemove', (e) => {
        const lp = toLogical(e.clientX, e.clientY);
        onPointerMove(lp.x, lp.y);
    });

    canvas.addEventListener('mouseup', (e) => {
        if (e.button !== 0) return;
        const lp = toLogical(e.clientX, e.clientY);
        onPointerUp(lp.x, lp.y);
    });

    // Mouse leaving the window while dragging = drop
    window.addEventListener('mouseup', (e) => {
        if (!drag) return;
        const lp = toLogical(e.clientX, e.clientY);
        onPointerUp(lp.x, lp.y);
    });

    canvas.addEventListener('dblclick', (e) => {
        const lp  = toLogical(e.clientX, e.clientY);
        const hit = hitTest(lp.x, lp.y);
        if (!hit) return;
        if (hit.type === 'waste')    autoMoveToFoundation({ type: 'waste' });
        else if (hit.type === 'tableau') autoMoveToFoundation({ type: 'tableau', col: hit.col });
    });

    // ── Canvas — touch ────────────────────────────────────────
    canvas.addEventListener('touchstart', (e) => {
        e.preventDefault();
        const t  = e.changedTouches[0];
        const lp = toLogical(t.clientX, t.clientY);
        const now = Date.now();

        // Double-tap detection (within 300 ms, within ~30 logical px)
        const dx = lp.x - lastTapX;
        const dy = lp.y - lastTapY;
        const doubleTap = (now - lastTapTime < 300) &&
                          (Math.sqrt(dx * dx + dy * dy) < 30);

        if (doubleTap) {
            lastTapTime = 0;
            const hit = hitTest(lp.x, lp.y);
            if (!hit) return;
            if (hit.type === 'waste')    autoMoveToFoundation({ type: 'waste' });
            else if (hit.type === 'tableau') autoMoveToFoundation({ type: 'tableau', col: hit.col });
            return;
        }

        lastTapTime = now;
        lastTapX    = lp.x;
        lastTapY    = lp.y;

        onPointerDown(lp.x, lp.y, true);
    }, { passive: false });

    canvas.addEventListener('touchmove', (e) => {
        e.preventDefault();
        const t  = e.changedTouches[0];
        const lp = toLogical(t.clientX, t.clientY);
        onPointerMove(lp.x, lp.y);
    }, { passive: false });

    canvas.addEventListener('touchend', (e) => {
        e.preventDefault();
        const t  = e.changedTouches[0];
        const lp = toLogical(t.clientX, t.clientY);
        onPointerUp(lp.x, lp.y);
    }, { passive: false });

    // ── Pause timer when page is hidden ──────────────────────
    document.addEventListener('visibilitychange', () => {
        if (document.hidden) {
            stopTimer();
        } else if (state && !state.won && !state.autoCompleting) {
            startTimer();
        }
    });
}

// --- State Serialization ---
// layout: flags(1) passes(1) score-i32le(4) elapsed-u24le(3) found×4 stock_len stock… waste_len waste… tabLens×7 tab… fnv32(4)
// card byte: bit7=0 bits6-5=suit_idx bits4-1=(rank-1) bit0=faceUp → URL-safe base64 (no padding)

const _SI = { S: 0, H: 1, C: 2, D: 3 };
const _SD = ['standard', 'vegas', 'none'];

function _fnv32(buf) {
    let h = 0x811c9dc5;
    for (const b of buf) h = Math.imul(h ^ b, 0x01000193) >>> 0;
    return h;
}

function _pack(s) {
    const tl = s.tableau.map(c => c.length);
    const buf = new Uint8Array(26 + s.stock.length + s.waste.length + tl.reduce((a, b) => a + b, 0));
    let p = 0;
    const B = v => buf[p++] = v;  // Uint8Array auto-masks to 8 bits
    const card = c => (_SI[c.suit] << 5) | ((c.rank - 1) << 1) | (c.faceUp ? 1 : 0);

    B(((s.drawCount > 1) << 7) | (_SD.indexOf(s.scoring) << 5) | (s.won ? 16 : 0) | (s.autoCompleting ? 8 : 0));
    B(Math.min(s.passes, 255));
    const sc = s.score | 0;
    B(sc); B(sc >> 8); B(sc >> 16); B(sc >> 24);
    const el = s.elapsed >>> 0;
    B(el); B(el >> 8); B(el >> 16);
    for (const f of s.foundations) B(f.length ? (_SI[f[0].suit] << 4) | f.length : 0xF0);
    B(s.stock.length); for (const c of s.stock) B(card(c));
    B(s.waste.length); for (const c of s.waste) B(card(c));
    for (const l of tl) B(l);
    for (const col of s.tableau) for (const c of col) B(card(c));
    const cs = _fnv32(buf.subarray(0, p));
    B(cs); B(cs >> 8); B(cs >> 16); B(cs >> 24);
    return buf;
}

function _unpack(buf) {
    if (buf.length < 26) throw new Error('Truncated');
    const de = buf.length - 4;
    const cs = buf[de] | (buf[de+1] << 8) | (buf[de+2] << 16) | (buf[de+3] << 24);
    if ((_fnv32(buf.subarray(0, de)) | 0) !== (cs | 0)) throw new Error('Checksum');
    let p = 0;
    const flags = buf[p++], si = (flags >> 5) & 3;
    if (si > 2) throw new Error('Bad scoring');
    const passes  = buf[p++];
    const score   = buf[p] | (buf[p+1] << 8) | (buf[p+2] << 16) | (buf[p+3] << 24); p += 4;
    const elapsed = buf[p] | (buf[p+1] << 8) | (buf[p+2] << 16); p += 3;
    const foundations = Array.from({ length: 4 }, () => {
        const fb = buf[p++], sn = fb >> 4, cnt = fb & 15;
        if (sn === 15) { if (cnt) throw new Error('Bad foundation'); return []; }
        if (sn > 3 || !cnt || cnt > 13) throw new Error('Bad foundation');
        return Array.from({ length: cnt }, (_, i) => ({ suit: SUITS[sn], rank: i + 1, faceUp: true }));
    });
    const read = n => {
        if (p + n > de) throw new Error('Truncated');
        return Array.from({ length: n }, () => {
            const b = buf[p++], c = { suit: SUITS[(b >> 5) & 3], rank: ((b >> 1) & 15) + 1, faceUp: !!(b & 1) };
            if (c.rank > 13) throw new Error('Bad card');
            return c;
        });
    };
    if (p + 9 > de) throw new Error('Truncated');
    const stock = read(buf[p++]), waste = read(buf[p++]);
    const tableau = Array.from({ length: 7 }, () => buf[p++]).map(read);
    if (p !== de) throw new Error('Extra bytes');
    const all = [...stock, ...waste, ...foundations.flat(), ...tableau.flat()];
    if (all.length !== 52 || new Set(all.map(c => c.suit + c.rank)).size !== 52) throw new Error('Bad deck');
    return { stock, waste, foundations, tableau, passes, score, elapsed,
             drawCount: flags >> 7 ? 3 : 1, scoring: _SD[si],
             won: !!(flags & 16), autoCompleting: !!(flags & 8) };
}

function serialize(state) {
    try {
        const buf = _pack(state);
        let s = ''; for (const b of buf) s += String.fromCharCode(b);
        return btoa(s).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
    } catch(e) { console.error('serialize:', e); return null; }
}

function deserialize(str) {
    try {
        const s = atob(str.replace(/-/g, '+').replace(/_/g, '/') + '=='.slice(0, (4 - str.length % 4) % 4));
        return _unpack(Uint8Array.from(s, c => c.charCodeAt(0)));
    } catch(e) { console.error('deserialize:', e); return null; }
}

document.addEventListener('DOMContentLoaded', init);
