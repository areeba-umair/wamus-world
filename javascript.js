/* ═══════════════════════════════════════════════════════════════
   WUMPUS WORLD — script.js
   Knowledge-Based Agent with Propositional Logic + Resolution
   ═══════════════════════════════════════════════════════════════ */

// ── Stars background ──────────────────────────────────────────
(function () {
  const container = document.getElementById('stars');
  for (let i = 0; i < 60; i++) {
    const star = document.createElement('div');
    star.className = 'star';
    const size = Math.random() * 2 + 1;
    star.style.cssText =
      `width:${size}px;height${size}px;` +
      `top:${Math.random() * 100}%;left:${Math.random() * 100}%;` +
      `background:#fff;--d:${2 + Math.random() * 4}s;--delay:${Math.random() * 4}s`;
    container.appendChild(star);
  }
})();


/* ═══════════════════════════════════════════════════════════════
   GLOBAL STATE
   ═══════════════════════════════════════════════════════════════ */
let R, C, grid, agent, gameOver, inferenceSteps, moveCount;
let autoTimer = null, autoRunning = false;

/**
 * Knowledge Base
 *   clauses  : array of CNF clause arrays (each clause = array of literal strings)
 *   facts    : Set of atoms known TRUE
 *   negFacts : Set of atoms known FALSE
 */
const KB = {
  clauses: [],
  facts: new Set(),
  negFacts: new Set()
};


/* ═══════════════════════════════════════════════════════════════
   HELPERS
   ═══════════════════════════════════════════════════════════════ */

/** Random integer 0 … n-1 */
function rnd(n) { return Math.floor(Math.random() * n); }

/**
 * Grid coordinates displayed as (row, col) starting from bottom-left.
 * Internal grid[0][0] = top-left, so displayed row = R - internal_r.
 */
function rc(r, c) { return '(' + (R - r) + ',' + (c + 1) + ')'; }

/** Get valid orthogonal neighbors of cell (r,c) */
function neighbors(r, c) {
  const out = [];
  if (r > 0)   out.push([r - 1, c]);
  if (r < R-1) out.push([r + 1, c]);
  if (c > 0)   out.push([r, c - 1]);
  if (c < C-1) out.push([r, c + 1]);
  return out;
}

/** Build a propositional atom string, e.g. "P_2_3" */
function atom(type, r, c) { return type + '_' + r + '_' + c; }

/** Negate a literal: "P_1_2" ↔ "~P_1_2" */
function negate(lit) { return lit.startsWith('~') ? lit.slice(1) : '~' + lit; }


/* ═══════════════════════════════════════════════════════════════
   KNOWLEDGE BASE OPERATIONS
   ═══════════════════════════════════════════════════════════════ */

/**
 * TELL: Add a CNF clause to the KB.
 * Skips tautologies and duplicate clauses.
 */
function addClause(lits) {
  const set = new Set(lits);
  // Tautology check: clause contains both L and ¬L
  for (const l of set) {
    if (set.has(negate(l))) return;
  }
  const norm = JSON.stringify([...set].sort());
  if (!KB.clauses.find(cl => JSON.stringify([...cl].sort()) === norm))
    KB.clauses.push([...set]);
}

/**
 * TELL Breeze percept at (r,c).
 * Breeze ⟺ at least one adjacent Pit.
 * In CNF:
 *   B ⇒ (P_n1 ∨ P_n2 ∨ …)     →  ¬B ∨ P_n1 ∨ P_n2 ∨ …
 *   P_ni ⇒ B                   →  ¬P_ni ∨ B
 *   ¬B ⇒ ¬P_ni (for each ni)   →  ¬P_ni  (unit clause)
 */
function tellBreeze(r, c, hasBreeze) {
  const bAtom = atom('B', r, c);
  const pitAtoms = neighbors(r, c).map(([nr, nc]) => atom('P', nr, nc));

  if (hasBreeze) {
    KB.facts.add(bAtom);
    if (pitAtoms.length) addClause(['~' + bAtom, ...pitAtoms]);
    pitAtoms.forEach(p => addClause(['~' + p, bAtom]));
  } else {
    KB.negFacts.add(bAtom);
    pitAtoms.forEach(p => {
      KB.negFacts.add(p);
      addClause(['~' + p]);   // unit clause: no pit here
    });
  }
}

/**
 * TELL Stench percept at (r,c).
 * Stench ⟺ at least one adjacent Wumpus.
 */
function tellStench(r, c, hasStench) {
  const sAtom = atom('S', r, c);
  const wAtoms = neighbors(r, c).map(([nr, nc]) => atom('W', nr, nc));

  if (hasStench) {
    KB.facts.add(sAtom);
    if (wAtoms.length) addClause(['~' + sAtom, ...wAtoms]);
    wAtoms.forEach(w => addClause(['~' + w, sAtom]));
  } else {
    KB.negFacts.add(sAtom);
    wAtoms.forEach(w => {
      KB.negFacts.add(w);
      addClause(['~' + w]);
    });
  }
}

/**
 * TELL that cell (r,c) is safe (agent just visited it).
 * Adds unit clauses ¬P_r_c and ¬W_r_c.
 */
function tellSafe(r, c) {
  KB.negFacts.add(atom('P', r, c));
  KB.negFacts.add(atom('W', r, c));
  addClause(['~' + atom('P', r, c)]);
  addClause(['~' + atom('W', r, c)]);
}


/* ═══════════════════════════════════════════════════════════════
   RESOLUTION REFUTATION
   ═══════════════════════════════════════════════════════════════ */

/**
 * ASK: Prove ¬queryAtom using Resolution Refutation.
 *
 * Strategy:
 *   To prove ¬Q, assume Q (add unit clause [Q]),
 *   then repeatedly resolve clause pairs.
 *   If we derive the empty clause → contradiction → ¬Q is proved.
 *
 * @param {string} queryAtom - atom to disprove (e.g. "P_1_2")
 * @returns {{ proved: boolean, steps: number }}
 */
function proveNegation(queryAtom) {
  // Working set = KB clauses + assumption [queryAtom]
  let clauses = [...KB.clauses.map(c => [...c]), [queryAtom]];
  let steps = 0;
  const LIMIT = 300;
  let changed = true;

  while (changed && steps < LIMIT) {
    changed = false;
    const newClauses = [];

    for (let i = 0; i < clauses.length && steps < LIMIT; i++) {
      for (let j = i + 1; j < clauses.length && steps < LIMIT; j++) {
        steps++;
        inferenceSteps++;

        const resolvent = resolve(clauses[i], clauses[j]);
        if (resolvent === null) continue;           // no resolution possible
        if (resolvent.length === 0) {               // empty clause = contradiction!
          updateMetrics();
          return { proved: true, steps };
        }

        // Add resolvent if not already present
        const norm = JSON.stringify([...resolvent].sort());
        const alreadyHave =
          clauses.some(cl => JSON.stringify([...cl].sort()) === norm) ||
          newClauses.some(cl => JSON.stringify([...cl].sort()) === norm);

        if (!alreadyHave) {
          newClauses.push(resolvent);
          changed = true;
        }
      }
    }
    clauses = [...clauses, ...newClauses];
  }

  updateMetrics();
  return { proved: false, steps };
}

/**
 * Try to resolve two clauses on one complementary literal pair.
 * Returns the resolvent, null if no resolution possible, or
 * [] (empty array) if contradiction found.
 *
 * @param {string[]} c1
 * @param {string[]} c2
 * @returns {string[]|null}
 */
function resolve(c1, c2) {
  for (const lit of c1) {
    const neg = negate(lit);
    if (c2.includes(neg)) {
      const resolvent = [
        ...new Set([
          ...c1.filter(l => l !== lit),
          ...c2.filter(l => l !== neg)
        ])
      ];
      // Tautology check on resolvent
      for (const l of resolvent) {
        if (resolvent.includes(negate(l))) return null;
      }
      return resolvent;
    }
  }
  return null; // no complementary literal found
}


/* ═══════════════════════════════════════════════════════════════
   ENVIRONMENT SETUP
   ═══════════════════════════════════════════════════════════════ */

/** Compute breeze / stench / glitter percepts for every cell */
function computePercepts() {
  for (let r = 0; r < R; r++) {
    for (let c = 0; c < C; c++) {
      grid[r][c].breeze = false;
      grid[r][c].stench = false;
      neighbors(r, c).forEach(([nr, nc]) => {
        if (grid[nr][nc].pit)    grid[r][c].breeze = true;
        if (grid[nr][nc].wumpus) grid[r][c].stench = true;
      });
      grid[r][c].glitter = grid[r][c].gold;
    }
  }
}

/**
 * Start a new episode:
 *   - Read grid size from inputs
 *   - Randomly place pits, wumpus, gold
 *   - Reset KB and metrics
 */
function initGame() {
  // Stop any running auto-play
  if (autoTimer) {
    clearInterval(autoTimer);
    autoTimer = null;
    autoRunning = false;
    document.getElementById('btn-auto').textContent = '⚡ AUTO RUN';
  }

  // Read dimensions
  R = Math.max(3, Math.min(6, +document.getElementById('in-rows').value));
  C = Math.max(3, Math.min(6, +document.getElementById('in-cols').value));

  // Reset state
  agent = { r: R - 1, c: 0 };
  gameOver = false;
  inferenceSteps = 0;
  moveCount = 0;
  KB.clauses = [];
  KB.facts = new Set();
  KB.negFacts = new Set();

  // Build empty grid
  grid = [];
  for (let r = 0; r < R; r++) {
    grid[r] = [];
    for (let c = 0; c < C; c++) {
      grid[r][c] = {
        pit: false, wumpus: false, gold: false,
        visited: false, safe: false,
        knownPit: false, knownWumpus: false,
        breeze: false, stench: false, glitter: false
      };
    }
  }

  // Start cell is always safe
  grid[R-1][0].safe = true;
  grid[R-1][0].visited = true;

  // Place pits (≈15% of cells, minimum 1)
  const numPits = Math.max(1, Math.floor(R * C * 0.15 + 1));
  let placed = 0;
  while (placed < numPits) {
    const r = rnd(R), c = rnd(C);
    if ((r === R-1 && c === 0) || grid[r][c].pit) continue;
    grid[r][c].pit = true;
    placed++;
  }

  // Place wumpus
  let wr, wc;
  do { wr = rnd(R); wc = rnd(C); }
  while ((wr === R-1 && wc === 0) || grid[wr][wc].pit);
  grid[wr][wc].wumpus = true;

  // Place gold
  let gr, gc;
  do { gr = rnd(R); gc = rnd(C); }
  while ((gr === R-1 && gc === 0) || (gr === wr && gc === wc) || grid[gr][gc].pit);
  grid[gr][gc].gold = true;

  computePercepts();
  setStatus('Episode started — Agent at ' + rc(agent.r, agent.c) + '. Use STEP or AUTO RUN.');
  updateMetrics();
  renderGrid();
  clearLog();
  addLog('New episode: ' + R + '×' + C + ' grid | Agent → ' + rc(agent.r, agent.c), 'info');
  perceiveAndTell();
}


/* ═══════════════════════════════════════════════════════════════
   AGENT PERCEPTION & INFERENCE
   ═══════════════════════════════════════════════════════════════ */

/**
 * Perceive current cell, update KB, infer safety of neighbors.
 */
function perceiveAndTell() {
  const { r, c } = agent;
  const cell = grid[r][c];

  // TELL KB about current cell
  tellSafe(r, c);
  tellBreeze(r, c, cell.breeze);
  tellStench(r, c, cell.stench);

  // Update percept badge display
  const badges = [];
  if (cell.breeze)  badges.push('<span class="badge breeze">~ BREEZE</span>');
  if (cell.stench)  badges.push('<span class="badge stench">Ψ STENCH</span>');
  if (cell.glitter) badges.push('<span class="badge glitter">✦ GLITTER</span>');
  if (!badges.length) badges.push('<span class="badge none">NONE</span>');
  document.getElementById('percept-display').innerHTML = badges.join('');

  // ASK KB about each unvisited neighbor
  neighbors(r, c).forEach(([nr, nc]) => {
    if (!grid[nr][nc].visited) askSafe(nr, nc);
  });

  updateCNFDisplay();
  updateProgressBar();
}

/**
 * ASK: Use Resolution Refutation to determine if cell (r,c) is safe.
 * Marks cell.safe = true if both ¬Pit and ¬Wumpus are proved.
 */
function askSafe(r, c) {
  if (grid[r][c].safe) return;

  const pAtom = atom('P', r, c);
  const wAtom = atom('W', r, c);

  // Fast path: already in negFacts
  if (KB.negFacts.has(pAtom) && KB.negFacts.has(wAtom)) {
    addLog('KB direct: ' + rc(r, c) + ' is SAFE ✓', 'safe');
    grid[r][c].safe = true;
    renderGrid();
    return;
  }

  // Full Resolution Refutation
  const rP = proveNegation(pAtom);
  const rW = proveNegation(wAtom);

  addLog(
    'Resolution ' + rc(r,c) +
    ': ¬Pit=' + rP.proved + '(' + rP.steps + 'st)' +
    ' ¬Wumpus=' + rW.proved + '(' + rW.steps + 'st)',
    'infer'
  );

  if (rP.proved && rW.proved) {
    addLog('PROVED SAFE: ' + rc(r, c) + ' ✓', 'safe');
    grid[r][c].safe = true;
  }
  renderGrid();
}


/* ═══════════════════════════════════════════════════════════════
   AGENT MOVEMENT
   ═══════════════════════════════════════════════════════════════ */

/**
 * Execute one agent step:
 *   1. Pick up gold if present
 *   2. Move to a proved-safe unvisited neighbor
 *   3. Backtrack if no safe neighbor exists
 *   4. Take a calculated risk if forced
 */
function agentStep() {
  if (gameOver) return;
  const { r, c } = agent;

  // Collect gold
  if (grid[r][c].gold) {
    grid[r][c].gold = false;
    grid[r][c].glitter = false;
    addLog('✦ Gold collected at ' + rc(r, c) + '!', 'safe');
    setStatus('Gold collected! Continuing exploration...');
    computePercepts();
    renderGrid();
    return;
  }

  // Safe unvisited neighbors
  const safeNeighbors = neighbors(r, c).filter(
    ([nr, nc]) => !grid[nr][nc].visited && grid[nr][nc].safe
  );

  if (safeNeighbors.length > 0) {
    const [nr, nc] = safeNeighbors[rnd(safeNeighbors.length)];
    moveAgent(nr, nc);
    moveCount++;
    return;
  }

  // No safe neighbor — try backtracking
  const unvisited = neighbors(r, c).filter(([nr, nc]) => !grid[nr][nc].visited);

  if (unvisited.length === 0) {
    const bt = findBacktrack();
    if (bt) { moveAgent(bt[0], bt[1]); moveCount++; }
    else { endGame(false, '🏁 All reachable safe cells explored!'); }
    return;
  }

  // Try to infer more before giving up
  unvisited.forEach(([nr, nc]) => askSafe(nr, nc));
  const safeAfterInfer = neighbors(r, c).filter(
    ([nr, nc]) => !grid[nr][nc].visited && grid[nr][nc].safe
  );

  if (safeAfterInfer.length > 0) {
    const [nr, nc] = safeAfterInfer[0];
    moveAgent(nr, nc);
    moveCount++;
  } else {
    // Calculated risk: move to least-suspicious unvisited neighbor
    addLog('No proved-safe moves. Taking calculated risk...', 'info');
    moveAgent(unvisited[0][0], unvisited[0][1]);
    moveCount++;
  }

  updateMetrics();
}

/**
 * Move agent to (nr, nc). Check for pit/wumpus death.
 */
function moveAgent(nr, nc) {
  agent = { r: nr, c: nc };
  const cell = grid[nr][nc];
  cell.visited = true;
  cell.safe = true;

  addLog('→ Moved to ' + rc(nr, nc), 'info');

  if (cell.pit) {
    cell.knownPit = true;
    endGame(true, '💀 Agent fell into a pit at ' + rc(nr, nc) + '!');
    return;
  }
  if (cell.wumpus) {
    cell.knownWumpus = true;
    endGame(true, '💀 Wumpus got the agent at ' + rc(nr, nc) + '!');
    return;
  }

  perceiveAndTell();
  renderGrid();
  setStatus(
    'Agent at ' + rc(nr, nc) +
    (cell.breeze  ? ' | ~ Breeze'  : '') +
    (cell.stench  ? ' | Ψ Stench'  : '') +
    (cell.glitter ? ' | ✦ Gold!'   : '')
  );
}

/**
 * BFS to find a visited safe cell that is adjacent to a safe unvisited cell.
 * Used for backtracking.
 */
function findBacktrack() {
  const queue = [[agent.r, agent.c]];
  const seen = new Set([agent.r + ',' + agent.c]);

  while (queue.length) {
    const [r, c] = queue.shift();
    const hasSafeTarget = neighbors(r, c).some(
      ([nr, nc]) => !grid[nr][nc].visited && grid[nr][nc].safe
    );
    if (hasSafeTarget && !(r === agent.r && c === agent.c)) return [r, c];

    neighbors(r, c)
      .filter(([nr, nc]) => grid[nr][nc].visited && !seen.has(nr + ',' + nc))
      .forEach(([nr, nc]) => {
        seen.add(nr + ',' + nc);
        queue.push([nr, nc]);
      });
  }
  return null;
}

/**
 * End the current episode.
 */
function endGame(died, msg) {
  gameOver = true;
  if (autoTimer) {
    clearInterval(autoTimer);
    autoTimer = null;
    autoRunning = false;
    document.getElementById('btn-auto').textContent = '⚡ AUTO RUN';
  }
  setStatus(msg);
  addLog(msg, died ? 'danger' : 'safe');
  // Reveal all hazards
  for (let r = 0; r < R; r++) {
    for (let c = 0; c < C; c++) {
      if (grid[r][c].pit)    grid[r][c].knownPit = true;
      if (grid[r][c].wumpus) grid[r][c].knownWumpus = true;
    }
  }
  renderGrid();
}

/**
 * Toggle auto-run mode (agent steps every 700ms).
 */
function autoRun() {
  if (gameOver) { initGame(); return; }
  if (autoRunning) {
    clearInterval(autoTimer);
    autoTimer = null;
    autoRunning = false;
    document.getElementById('btn-auto').textContent = '⚡ AUTO RUN';
    return;
  }
  autoRunning = true;
  document.getElementById('btn-auto').textContent = '⏹ STOP';
  autoTimer = setInterval(() => {
    if (gameOver) {
      clearInterval(autoTimer);
      autoTimer = null;
      autoRunning = false;
      document.getElementById('btn-auto').textContent = '⚡ AUTO RUN';
      return;
    }
    agentStep();
  }, 700);
}


/* ═══════════════════════════════════════════════════════════════
   RENDERING
   ═══════════════════════════════════════════════════════════════ */

/** Render the full grid into #grid */
function renderGrid() {
  const g = document.getElementById('grid');
  g.style.gridTemplateColumns = 'repeat(' + C + ', 82px)';
  g.innerHTML = '';

  for (let r = 0; r < R; r++) {
    for (let c = 0; c < C; c++) {
      const cell = grid[r][c];
      const div = document.createElement('div');

      // Cell class
      let cls = 'cell ';
      if (cell.knownPit || cell.knownWumpus) {
        cls += 'danger';
      } else if (r === agent.r && c === agent.c) {
        cls += 'visited agent';
      } else if (cell.visited) {
        cls += 'visited';
      } else if (cell.safe) {
        cls += 'safe';
      } else {
        cls += 'unknown';
      }
      div.className = cls;

      // Coordinate label
      const coord = document.createElement('div');
      coord.className = 'coord';
      coord.textContent = rc(r, c);

      // Icons
      const icons = document.createElement('div');
      icons.className = 'icons';
      let ic = '';
      if (r === agent.r && c === agent.c)   ic = '🤖';
      else if (cell.knownWumpus)             ic = '👾';
      else if (cell.knownPit)                ic = '🕳';
      if (cell.gold && !cell.knownPit && !cell.knownWumpus) ic += '💰';
      icons.textContent = ic;

      // Percept symbols on visited cells
      const perc = document.createElement('div');
      perc.className = 'percepts';
      const pt = [];
      if (cell.visited) {
        if (cell.breeze) pt.push('~');
        if (cell.stench) pt.push('Ψ');
      }
      perc.textContent = pt.join(' ');

      div.appendChild(coord);
      div.appendChild(icons);
      div.appendChild(perc);
      g.appendChild(div);
    }
  }
}

/** Update the three metric numbers */
function updateMetrics() {
  document.getElementById('m-steps').textContent = inferenceSteps;
  document.getElementById('m-moves').textContent = moveCount;
  document.getElementById('m-safe').textContent =
    grid.flat().filter(c => c.safe && !c.pit && !c.wumpus).length;
}

/** Update exploration progress bar */
function updateProgressBar() {
  const total   = R * C;
  const visited = grid.flat().filter(c => c.visited).length;
  document.getElementById('progress-bar').style.width =
    Math.round((visited / total) * 100) + '%';
}

/** Show last 14 CNF clauses with human-readable atom labels */
function updateCNFDisplay() {
  const d = document.getElementById('cnf-display');
  const recent = KB.clauses.slice(-14);
  d.textContent = recent.map(cl =>
    '(' + cl.map(l => {
      const neg  = l.startsWith('~');
      const base = neg ? l.slice(1) : l;
      const parts = base.split('_');
      const pretty = parts[0] + rc(+parts[1], +parts[2]);
      return (neg ? '¬' : '') + pretty;
    }).join(' ∨ ') + ')'
  ).join('\n') +
  (KB.clauses.length > 14 ? '\n... ' + (KB.clauses.length - 14) + ' more clauses' : '');
}

/** Append a timestamped line to the inference log */
function addLog(msg, type = 'info') {
  const d = document.getElementById('log');
  const el = document.createElement('div');
  el.className = 'log-' + type;
  const ts = new Date().toLocaleTimeString('en', {
    hour12: false, hour: '2-digit', minute: '2-digit', second: '2-digit'
  });
  el.textContent = '[' + ts + '] ' + msg;
  d.appendChild(el);
  d.scrollTop = d.scrollHeight;
}

function clearLog()       { document.getElementById('log').innerHTML = ''; }
function setStatus(msg)   { document.getElementById('status').textContent = msg; }

// ── Auto-start on page load ───────────────────────────────────
initGame();
