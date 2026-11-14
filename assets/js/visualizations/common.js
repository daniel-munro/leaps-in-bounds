// Shared data loading for the visualizations page.
// Loads the public export in /data and builds, per constant, its numeric
// history of bounds (discovered in the literature or by a certificate) in
// order with the running lower/upper bounds after each.

const LOWER = 'lower_bound';
const UPPER = 'upper_bound';
const COLORS = { lower: '#2a78d6', upper: '#eb6834', solved: '#1a9e5c', range: '#8794a1' };

// Fractional year; year-only dates sit mid-year, month-only mid-month.
function parseDate(s) {
  if (!s) return null;
  const [y, m, d] = s.split('-').map(Number);
  if (!m) return y + 0.5;
  if (!d) return y + (m - 0.5) / 12;
  const days = new Date(y, m, 0).getDate();
  return y + (m - 1) / 12 + (d - 0.5) / (12 * days);
}

function formatDate(s) {
  if (!s) return 'undated';
  const [y, m, d] = s.split('-');
  if (!m) return y;
  const month = new Date(2000, +m - 1, 1).toLocaleString('en', { month: 'short' });
  return d ? `${+d} ${month} ${y}` : `${month} ${y}`;
}

// Render $...$ segments with KaTeX.
function texToHtml(s) {
  return s.replace(/\$([^$]+)\$/g, (_, tex) => {
    try { return katex.renderToString(tex, { throwOnError: false }); } catch { return tex; }
  });
}

async function loadData() {
  const [updates, constants, groups, sources] = await Promise.all(
    ['history', 'constants', 'constant_groups', 'sources'].map(n => fetch(`${window.SITE_BASEURL || ""}/data/${n}.json`).then(r => r.json()))
  );
  const sourceById = new Map(Object.entries(sources));
  const byConst = d3.group(updates, u => u.constant);
  const list = [];
  for (const [id, c] of Object.entries(constants)) {
    const raw = (byConst.get(id) || []).filter(u => u.value && u.value.decimal_approx != null);
    // Undated updates come first in the data; keep file order within equal dates.
    const ups = raw.map((u, i) => ({ ...u, i, t: parseDate(u.date), v: u.value.decimal_approx, isLower: u.type === LOWER }))
      .sort((a, b) => ((a.t ?? -Infinity) - (b.t ?? -Infinity)) || a.i - b.i);
    let lo = -Infinity, hi = Infinity, solved = false;
    for (const u of ups) {
      const before = u.isLower ? lo : hi;
      if (u.isLower) lo = Math.max(lo, u.v); else hi = Math.min(hi, u.v);
      u.improves = (u.isLower ? lo : hi) !== before;
      u.lo = lo; u.hi = hi;
      u.solves = !solved && Number.isFinite(hi - lo) && hi - lo <= 1e-9 * Math.max(1, Math.abs(hi));
      if (u.solves) solved = true;
      if (u.discovery_kind === 'certificate') {
        u.sourceName = `Certificate ${u.discovery}`;
      } else {
        const src = sourceById.get(u.discovery) || sourceById.get(u.via);
        u.sourceName = src ? src.string : (u.discovery || u.via || '');
      }
    }
    const dated = ups.filter(u => u.t != null);
    list.push({ id, name: c.name, group: c.group, groupName: groups[c.group]?.name ?? c.group, updates: ups, dated });
    for (const u of ups) u.constant = list[list.length - 1];
  }
  // Groups in order of first appearance among constants.
  const groupOrder = [...new Set(list.map(c => c.group))];
  return { constants: list, groupOrder, groups };
}

const tooltip = (() => {
  let el;
  return {
    show(html, event) {
      el ??= d3.select('body').append('div').attr('class', 'viz-tooltip');
      el.html(html).style('display', 'block');
      const { width, height } = el.node().getBoundingClientRect();
      let x = event.clientX + 14, y = event.clientY + 14;
      if (x + width > window.innerWidth - 8) x = event.clientX - width - 14;
      if (y + height > window.innerHeight - 8) y = event.clientY - height - 14;
      el.style('left', `${x}px`).style('top', `${y}px`);
    },
    hide() { el?.style('display', 'none'); },
  };
})();

function boundSymbol(u) {
  return u.isLower ? '≥' : '≤';
}
