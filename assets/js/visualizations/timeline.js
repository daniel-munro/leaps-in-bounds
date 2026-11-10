// Timeline: one row per constant (grouped), one mark per dated bound update.

function drawTimeline(root, data) {
  const constants = data.constants.filter(c => c.dated.length);
  const byGroup = d3.group(constants, c => c.group);
  const groupOrder = data.groupOrder.filter(g => byGroup.has(g));

  const width = root.node().clientWidth;
  const margin = { top: 8, right: 16, bottom: 28, left: 210 };
  const histH = 64, histGap = 14;
  const rowH = 1.7, minBand = 18, bandGap = 7;

  // Group bands, each constant a row inside its band.
  let y0 = margin.top + histH + histGap;
  const bands = groupOrder.map(g => {
    const cs = byGroup.get(g);
    const h = Math.max(minBand, cs.length * rowH);
    const band = { group: g, name: cs[0].groupName, y: y0, h, cs };
    cs.forEach((c, i) => { c.rowY = y0 + (cs.length === 1 ? h / 2 : (i + 0.5) * h / cs.length); });
    y0 += h + bandGap;
    return band;
  });
  const height = y0 + margin.bottom;

  const points = constants.flatMap(c => c.dated);
  const tMin = 1870, tMax = 2027;
  const plotL = margin.left, plotR = width - margin.right;

  // Two time scales: linear, and log of years before now (stretches recent decades).
  const scales = {
    linear: { f: t => t, ticks: d3.range(1880, 2027, 20).concat([2026]) },
    log: { f: t => -Math.log(tMax + 1 - t), ticks: [1875, 1900, 1950, 1975, 1990, 2000, 2010, 2015, 2020, 2023, 2025, 2026] },
  };
  let mode = 'log';
  const xOf = () => {
    const { f } = scales[mode];
    const s = d3.scaleLinear().domain([f(tMin), f(tMax)]).range([plotL, plotR]);
    return t => s(f(t));
  };
  let x = xOf();

  const svg = root.append('svg').attr('width', width).attr('height', height).attr('class', 'viz-svg');

  // Bands and labels
  const bandG = svg.append('g');
  bandG.selectAll('rect').data(bands).join('rect')
    .attr('x', plotL).attr('width', plotR - plotL).attr('y', b => b.y - 2).attr('height', b => b.h + 4)
    .attr('fill', (b, i) => i % 2 ? '#f6f7f8' : '#fbfbfc');
  bandG.selectAll('text').data(bands).join('text')
    .attr('x', plotL - 8).attr('y', b => b.y + b.h / 2).attr('dy', '0.35em')
    .attr('text-anchor', 'end').attr('class', 'viz-label')
    .text(b => b.name);

  // Axis and gridlines
  const axisG = svg.append('g');
  function drawAxis() {
    const ticks = scales[mode].ticks;
    axisG.selectAll('line').data(ticks, d => d).join('line')
      .attr('y1', margin.top + histH).attr('y2', height - margin.bottom)
      .attr('stroke', '#e3e5e8').attr('stroke-width', 1)
      .transition().duration(600).attr('x1', d => x(d)).attr('x2', d => x(d));
    axisG.selectAll('text').data(ticks, d => d).join('text')
      .attr('y', height - margin.bottom + 18).attr('text-anchor', 'middle').attr('class', 'viz-tick')
      .text(d => d)
      .transition().duration(600).attr('x', d => x(d));
  }

  // Histogram of updates per year, lower stacked under upper.
  const years = d3.range(tMin, tMax);
  const counts = d3.rollup(points, v => ({ lower: v.filter(u => u.isLower).length, upper: v.filter(u => !u.isLower).length }), u => Math.floor(u.t));
  const hist = years.map(y => ({ y, ...(counts.get(y) || { lower: 0, upper: 0 }) }));
  const hy = d3.scaleLinear().domain([0, d3.max(hist, d => d.lower + d.upper)]).range([margin.top + histH, margin.top]);
  const histG = svg.append('g');
  svg.append('text').attr('x', plotL - 8).attr('y', margin.top + histH / 2).attr('dy', '0.35em')
    .attr('text-anchor', 'end').attr('class', 'viz-label viz-muted').text('Updates per year');
  svg.append('text').attr('x', plotL + 4).attr('y', hy(hy.domain()[1]) + 10).attr('class', 'viz-tick viz-muted')
    .text(`${hy.domain()[1]} (max)`);
  function drawHist() {
    const w = d => Math.max(0.5, x(d.y + 1) - x(d.y) - (x(d.y + 1) - x(d.y) > 3 ? 1 : 0));
    histG.selectAll('rect.lo').data(hist).join('rect').attr('class', 'lo').attr('fill', COLORS.lower)
      .attr('y', d => hy(d.lower)).attr('height', d => hy(0) - hy(d.lower))
      .transition().duration(600).attr('x', d => x(d.y)).attr('width', w);
    histG.selectAll('rect.up').data(hist).join('rect').attr('class', 'up').attr('fill', COLORS.upper)
      .attr('y', d => hy(d.lower + d.upper)).attr('height', d => hy(d.lower) - hy(d.lower + d.upper))
      .transition().duration(600).attr('x', d => x(d.y)).attr('width', w);
  }

  // Lifelines: faint line from a constant's first to last dated update.
  const lifeG = svg.append('g').attr('stroke', '#c9ced4').attr('stroke-width', 0.6);
  // Marks
  const tri = d3.symbol().type(d3.symbolTriangle).size(26)();
  const diamond = d3.symbol().type(d3.symbolDiamond).size(46)();
  const markG = svg.append('g');
  const markOrder = points.slice().sort((a, b) => a.solves - b.solves);
  const marks = markG.selectAll('path').data(markOrder).join('path')
    .attr('d', u => u.solves ? diamond : tri)
    .attr('fill', u => u.solves ? COLORS.solved : u.isLower ? COLORS.lower : COLORS.upper)
    .attr('fill-opacity', u => u.improves ? 0.85 : 0.35)
    .attr('stroke', '#fff').attr('stroke-width', 0.5);

  function place(animate) {
    const sel = animate ? marks.transition().duration(600) : marks;
    sel.attr('transform', u => `translate(${x(u.t)},${u.constant.rowY}) rotate(${u.isLower ? 0 : 180})`);
    const ls = lifeG.selectAll('line').data(constants.filter(c => c.dated.length > 1)).join('line')
      .attr('y1', c => c.rowY).attr('y2', c => c.rowY);
    (animate ? ls.transition().duration(600) : ls)
      .attr('x1', c => x(c.dated[0].t)).attr('x2', c => x(c.dated[c.dated.length - 1].t));
    drawAxis(); drawHist();
    delaunay = d3.Delaunay.from(points, u => x(u.t), u => u.constant.rowY);
  }
  let delaunay;
  place(false);

  // Hover: nearest mark within reach, highlighting its constant's row.
  const hl = svg.append('g').style('pointer-events', 'none');
  svg.on('pointermove', event => {
    const [mx, my] = d3.pointer(event);
    const i = delaunay.find(mx, my);
    const u = points[i];
    if (!u || Math.hypot(x(u.t) - mx, u.constant.rowY - my) > 14) { tooltip.hide(); hl.selectAll('*').remove(); return; }
    const c = u.constant;
    hl.selectAll('line').data([c]).join('line').attr('x1', plotL).attr('x2', plotR)
      .attr('y1', c.rowY).attr('y2', c.rowY).attr('stroke', '#212529').attr('stroke-width', 0.8).attr('stroke-opacity', 0.5);
    hl.selectAll('circle').data(c.dated).join('circle').attr('cx', d => x(d.t)).attr('cy', c.rowY).attr('r', 5)
      .attr('fill', 'none').attr('stroke', '#212529').attr('stroke-width', d => d === u ? 1.6 : 0.6);
    const history = c.dated.map(d => `<div class="${d === u ? 'fw-semibold' : ''}">${formatDate(d.date)}: ${boundSymbol(d)} $${d.value.latex}$${d.solves ? ' (exact)' : ''}</div>`).join('');
    tooltip.show(`<div class="fw-semibold">${texToHtml(c.name)}</div>
      <div class="viz-tt-src">${u.sourceName}</div>
      <div class="viz-tt-hist">${texToHtml(history)}</div>`, event);
  }).on('pointerleave', () => { tooltip.hide(); hl.selectAll('*').remove(); });
  svg.on('click', event => {
    const [mx, my] = d3.pointer(event);
    const u = points[delaunay.find(mx, my)];
    if (u && Math.hypot(x(u.t) - mx, u.constant.rowY - my) <= 14) window.location.href = `${window.SITE_BASEURL || ""}/constants/${u.constant.id}/`;
  });

  return {
    setScale(m) { mode = m; x = xOf(); place(true); },
  };
}
