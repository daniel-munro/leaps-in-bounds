// Ranges: one column per constant, its possible values as a bar that shrinks
// as bounds improve. Positions count improvements, not their size: on each
// side, a constant's bounds are evenly spaced from the edge (its first bound)
// toward the center, which stands for the true value. If the true value is
// known (in hindsight), the bound equal to it sits at the center; if not, the
// unknown value is one more step past the last bound. A missing bound runs off
// the edge.

function drawRanges(root, controls, data, opts = {}) {
  root.selectAll('*').remove();
  const cols = [];
  for (const c of data.constants) {
    if (!c.dated.length) continue;
    const improving = c.updates.filter(u => u.improves);
    const lows = improving.filter(u => u.isLower), highs = improving.filter(u => !u.isLower);
    const last = c.updates[c.updates.length - 1];
    const solved = Number.isFinite(last.hi - last.lo) && last.hi - last.lo <= 1e-9 * Math.max(1, Math.abs(last.hi));
    // Position of the i-th improvement on a side with n of them, as distance from the edge.
    const step = (i, n) => solved ? (i === n - 1 ? 0.5 : i * 0.5 / (n - 1)) : i * 0.5 / n;
    const pos = new Map();
    lows.forEach((u, i) => pos.set(u, step(i, lows.length)));
    highs.forEach((u, i) => pos.set(u, 1 - step(i, highs.length)));
    // States over time, t = -Infinity for undated. lo/hi are positions, vlo/vhi values.
    const states = [{ t: -Infinity, lo: -Infinity, hi: Infinity, vlo: -Infinity, vhi: Infinity }];
    let lo = -Infinity, hi = Infinity;
    for (const u of c.updates) {
      if (pos.has(u)) { if (u.isLower) lo = pos.get(u); else hi = pos.get(u); }
      const t = u.t ?? -Infinity;
      const s = { t, lo, hi, vlo: u.lo, vhi: u.hi };
      const prev = states[states.length - 1];
      if (prev.t === t) states[states.length - 1] = { ...s, u: [prev.u, u].flat().filter(Boolean) };
      else states.push({ ...s, u: [u] });
    }
    const fin = states[states.length - 1];
    const progress = solved ? 2 : Number.isFinite(fin.hi - fin.lo) ? 1 - (fin.hi - fin.lo) : Number.isFinite(fin.lo) ? fin.lo - 1 : -1 - (1 - fin.hi);
    cols.push({ c, states, progress, family: c.family });
  }
  const byFamily = d3.group(cols, d => d.family);
  const familyOrder = data.familyOrder.filter(g => byFamily.has(g));

  const stateAt = (col, T) => {
    const i = d3.bisector(s => s.t).right(col.states, T) - 1;
    return col.states[Math.max(0, i)];
  };

  // Layout
  const width = root.node().clientWidth;
  const margin = { top: 14, right: 16, bottom: 120, left: 110 };
  const plotH = 380;
  const height = margin.top + plotH + margin.bottom;
  const gap = 5;
  const colW = (width - margin.left - margin.right - gap * (familyOrder.length - 1)) / cols.length;
  const y = d3.scaleLinear().domain([-0.2, 1.2]).range([margin.top + plotH, margin.top]);
  const clampY = v => y(Math.max(-0.2, Math.min(1.2, v)));

  let sortMode = opts.sort || 'family';
  function layout() {
    let x0 = margin.left;
    for (const g of familyOrder) {
      const cs = byFamily.get(g).slice();
      if (sortMode === 'progress') cs.sort((p, q) => d3.descending(p.progress, q.progress));
      cs.forEach((col, i) => { col.x = x0 + i * colW; });
      byFamily.get(g).x0 = x0; byFamily.get(g).x1 = x0 + cs.length * colW;
      x0 += cs.length * colW + gap;
    }
  }
  layout();

  const svg = root.append('svg').attr('width', width).attr('height', height).attr('class', 'viz-svg');
  const defs = svg.append('defs');
  for (const [id, y1, y2] of [['fade-top', '0%', '100%'], ['fade-bottom', '100%', '0%']]) {
    const g = defs.append('linearGradient').attr('id', id).attr('x1', 0).attr('x2', 0).attr('y1', y1).attr('y2', y2);
    g.append('stop').attr('offset', '0%').attr('stop-color', '#fff').attr('stop-opacity', 1);
    g.append('stop').attr('offset', '100%').attr('stop-color', '#fff').attr('stop-opacity', 0);
  }

  // Reference lines at the original bounds
  const refG = svg.append('g');
  for (const [v, label] of [[0, 'first lower bound'], [0.5, 'true value'], [1, 'first upper bound']]) {
    refG.append('line').attr('x1', margin.left).attr('x2', width - margin.right).attr('y1', y(v)).attr('y2', y(v))
      .attr('stroke', v === 0.5 ? COLORS.solved : '#adb5bd').attr('stroke-opacity', v === 0.5 ? 0.5 : 1).attr('stroke-dasharray', '3 3');
    refG.append('text').attr('x', margin.left - 8).attr('y', y(v)).attr('dy', '0.35em').attr('text-anchor', 'end')
      .attr('class', 'viz-tick viz-muted').text(label);
  }
  refG.append('text').attr('x', margin.left - 8).attr('y', y(1.2) + 6).attr('dy', '0.35em').attr('text-anchor', 'end').attr('class', 'viz-label viz-muted').text('+∞');
  refG.append('text').attr('x', margin.left - 8).attr('y', y(-0.2) - 6).attr('dy', '0.35em').attr('text-anchor', 'end').attr('class', 'viz-label viz-muted').text('−∞');

  const barG = svg.append('g');
  const markG = svg.append('g');
  // Fades into the unbounded zones above and below the original range.
  svg.append('rect').attr('x', margin.left).attr('width', width - margin.left - margin.right)
    .attr('y', y(1.2)).attr('height', y(1.06) - y(1.2)).attr('fill', 'url(#fade-top)').style('pointer-events', 'none');
  svg.append('rect').attr('x', margin.left).attr('width', width - margin.left - margin.right)
    .attr('y', y(-0.06)).attr('height', y(-0.2) - y(-0.06)).attr('fill', 'url(#fade-bottom)').style('pointer-events', 'none');

  // Family labels
  const labelG = svg.append('g');
  function drawLabels(animate) {
    const sel = labelG.selectAll('g').data(familyOrder).join(enter => {
      const g = enter.append('g');
      g.append('line').attr('stroke', '#adb5bd');
      g.append('text').attr('class', 'viz-tick').attr('text-anchor', 'end').attr('transform', 'rotate(-40)').attr('dy', '0.35em');
      return g;
    });
    sel.attr('transform', g => `translate(${(byFamily.get(g).x0 + byFamily.get(g).x1) / 2},${margin.top + plotH + 8})`);
    sel.select('line').attr('x1', g => byFamily.get(g).x0 - (byFamily.get(g).x0 + byFamily.get(g).x1) / 2)
      .attr('x2', g => byFamily.get(g).x1 - (byFamily.get(g).x0 + byFamily.get(g).x1) / 2).attr('y1', -4).attr('y2', -4);
    let lastX = -Infinity;
    sel.select('text').attr('x', -2).attr('y', 6).text(g => byFamily.get(g)[0].c.familyName)
      .attr('display', g => { const cx = (byFamily.get(g).x0 + byFamily.get(g).x1) / 2; if (cx - lastX < 15) return 'none'; lastX = cx; return null; });
  }
  drawLabels();

  // Frames
  const allT = [...new Set(cols.flatMap(col => col.states.map(s => s.t)).filter(Number.isFinite))].sort((p, q) => p - q);
  const firstYear = Math.floor(allT[0]), lastYear = Math.floor(allT[allT.length - 1]);
  const paces = {
    update: [-Infinity, ...allT].map(t => ({ T: t, label: t === -Infinity ? 'Before dated records' : null })),
    year: [{ T: -Infinity, label: 'Before dated records' }, ...d3.range(firstYear, lastYear + 1).map(yr => ({ T: yr + 1 - 1e-9, label: String(yr) }))],
  };
  // Label update frames with the date of their updates.
  const dateAt = new Map();
  for (const col of cols) for (const s of col.states) if (s.u && Number.isFinite(s.t)) for (const u of s.u) dateAt.set(s.t, formatDate(u.date));
  for (const f of paces.update) f.label ??= dateAt.get(f.T);

  let pace = opts.pace || 'year', frames = paces[pace], frame = 0, timer = null, speed = 1;
  let prevT = -Infinity, prevFrame = -1;

  function render(duration) {
    const T = frames[frame].T;
    const sel = barG.selectAll('rect').data(cols, d => d.c.id).join('rect').attr('width', Math.max(1, colW - (colW > 3 ? 1 : 0)));
    for (const col of cols) col.s = stateAt(col, T);
    const t = duration ? sel.transition().duration(duration).ease(d3.easeCubicOut) : sel;
    t.attr('x', d => d.x)
      .attr('y', d => clampY(d.s.hi) - (solved(d.s) ? 1.5 : 0))
      .attr('height', d => solved(d.s) ? 3 : Math.max(1, clampY(d.s.lo) - clampY(d.s.hi)))
      .attr('fill', d => solved(d.s) ? COLORS.solved : COLORS.range);

    // Updates in this frame: (previous frame, this frame].
    const fromT = frame > 0 ? frames[frame - 1].T : -Infinity;
    const inFrame = cols.flatMap(col => col.states.filter(s => s.t > fromT && s.t <= T && s.u).flatMap(s => s.u.filter(u => u.improves).map(u => ({ col, u }))));
    showTicker(frame > 0 ? inFrame : []);
    // Markers for bounds that changed, only when moving forward.
    markG.selectAll('*').interrupt().remove();
    if (T > prevT && frame === prevFrame + 1) {
      const changed = cols.flatMap(col => col.states.filter(s => s.t > prevT && s.t <= T && s.u).flatMap(s => s.u.filter(u => u.improves).map(u => ({ col, u }))));
      const tri = d3.symbol().type(d3.symbolTriangle).size(34)();
      markG.selectAll(null).data(changed).join('path').attr('d', tri)
        .attr('fill', d => d.u.solves ? COLORS.solved : d.u.isLower ? COLORS.lower : COLORS.upper)
        .attr('transform', d => {
          const s = d.col.s, v = d.u.isLower ? s.lo : s.hi;
          return `translate(${d.col.x + colW / 2},${clampY(v) + (d.u.isLower ? 7 : -7)}) rotate(${d.u.isLower ? 0 : 180})`;
        })
        .transition().delay(Math.max(150, duration)).duration(Math.max(500, duration * 3)).attr('opacity', 0).remove();
    }
    prevT = T; prevFrame = frame;
    controls.slider.property('value', frame);
    controls.date.text(frames[frame].label);
    const counts = d3.rollup(cols, v => v.length, d => solved(d.s) ? 'exact' : Number.isFinite(d.s.lo) && Number.isFinite(d.s.hi) ? 'bounded' : Number.isFinite(d.s.lo) || Number.isFinite(d.s.hi) ? 'half' : 'none');
    controls.stats.html(`<span><b>${counts.get('exact') || 0}</b> exact</span><span><b>${counts.get('bounded') || 0}</b> bounded</span><span><b>${counts.get('half') || 0}</b> one bound</span><span><b>${counts.get('none') || 0}</b> no bounds yet</span>`);
  }
  const solved = s => s.hi - s.lo <= 1e-9;

  function showTicker(changed) {
    if (!changed.length) { controls.ticker.html('<span class="viz-muted">No improvements</span>'); return; }
    const shown = changed.slice(-3).map(({ col, u }) => `<div>${texToHtml(col.c.name)} ${u.solves ? '=' : boundSymbol(u)} ${texToHtml('$' + u.value.latex + '$')}</div>`).join('');
    const more = changed.length > 3 ? `<div class="viz-muted">and ${changed.length - 3} more</div>` : '';
    controls.ticker.html(shown + more);
  }

  // Frames with no improvements pass quickly.
  const quiet = f => !cols.some(col => col.states.some(s => s.t > (f > 0 ? frames[f - 1].T : -Infinity) && s.t <= frames[f].T && s.u?.some(u => u.improves)));
  function step() {
    if (frame >= frames.length - 1) { stop(); return; }
    frame++;
    const ms = quiet(frame) ? frameMs() / 6 : frameMs();
    render(ms * 0.9);
    timer = setTimeout(step, ms);
  }
  const frameMs = () => (pace === 'year' ? 300 : 120) / speed;
  function play() {
    if (frame >= frames.length - 1) { frame = 0; prevT = -Infinity; render(0); }
    timer = setTimeout(step, frameMs());
    controls.play.text('Pause');
  }
  function stop() { clearTimeout(timer); timer = null; controls.play.text('Play'); }

  controls.slider.attr('max', frames.length - 1).on('input', function () {
    stop(); frame = +this.value; render(0);
  });
  controls.play.on('click', () => timer ? stop() : play());

  // Hover
  svg.on('pointermove', event => {
    const [mx, my] = d3.pointer(event);
    const col = cols.find(d => mx >= d.x && mx < d.x + colW);
    if (!col || my < margin.top || my > margin.top + plotH) { tooltip.hide(); return; }
    const s = col.s;
    const fmt = (v, inf) => Number.isFinite(v) ? d3.format(',.6~g')(v) : inf;
    const bounds = solved(s) ? `= ${fmt(s.vlo)}` : `${fmt(s.vlo, '−∞')} … ${fmt(s.vhi, '+∞')}`;
    const T = frames[frame].T;
    const history = col.c.updates.filter(u => u.improves).map(u => `<div class="${(u.t ?? -Infinity) > T ? 'viz-muted' : ''}">${u.date ? formatDate(u.date) : 'undated'}: ${u.solves ? '=' : boundSymbol(u)} $${u.value.latex}$</div>`).join('');
    tooltip.show(`<div class="fw-semibold">${texToHtml(col.c.name)}</div>
      <div class="viz-muted">${col.c.familyName}</div>
      <div>${frames[frame].label}: ${bounds}</div>
      <div class="viz-tt-hist mt-1">${texToHtml(history)}</div>`, event);
  }).on('pointerleave', () => tooltip.hide());

  frame = opts.T != null ? Math.max(0, d3.bisector(f => f.T).right(frames, opts.T) - 1) : frames.length - 1;
  prevT = frames[frame].T;
  render(0);
  controls.slider.attr('max', frames.length - 1).property('value', frame);

  return {
    setPace(p) {
      stop();
      const T = frames[frame].T;
      pace = p; frames = paces[p];
      frame = Math.max(0, d3.bisector(f => f.T).right(frames, T) - 1);
      controls.slider.attr('max', frames.length - 1);
      prevT = frames[frame].T; render(0);
    },
    setSort(m) { sortMode = m; layout(); drawLabels(); render(500); },
    setSpeed(v) { speed = v; if (timer) { stop(); play(); } },
  };
}
