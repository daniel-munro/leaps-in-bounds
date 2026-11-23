// Mark the family in view in the constants page's family menus: highlight it
// in the sidebar, keeping it in the sidebar's view, and name it in the
// dropdown bar.
document.addEventListener('DOMContentLoaded', () => {
  const links = [...document.querySelectorAll('.family-nav-link')];
  const ids = [...new Set(links.map(link => link.hash.slice(1)))];
  const headings = ids.map(id => document.getElementById(id)).filter(Boolean);
  const sidebar = document.querySelector('.family-sidebar');
  const current = document.querySelector('.family-bar-current');
  const bar = document.querySelector('.family-bar');
  const placeholder = current ? current.textContent : '';
  let active = null;

  const update = () => {
    // The last family whose heading is above the top fifth of the window
    const offset = Math.max(bar ? bar.getBoundingClientRect().bottom : 0, 0) + window.innerHeight / 5;
    let found = null;
    for (const heading of headings) {
      if (heading.getBoundingClientRect().top > offset) break;
      found = heading.id;
    }
    if (found === active) return;
    active = found;
    let name = placeholder;
    for (const link of links) {
      const on = link.hash === '#' + active;
      link.classList.toggle('active', on);
      if (on) {
        link.setAttribute('aria-current', 'location');
        name = link.textContent;
        // Scroll the sidebar, not the page, to show the link
        if (sidebar && sidebar.contains(link)) {
          const top = link.getBoundingClientRect().top - sidebar.getBoundingClientRect().top + sidebar.scrollTop;
          if (top < sidebar.scrollTop || top + link.offsetHeight > sidebar.scrollTop + sidebar.clientHeight) {
            sidebar.scrollTop = top - sidebar.clientHeight / 3;
          }
        }
      } else {
        link.removeAttribute('aria-current');
      }
    }
    if (current) current.textContent = name;
  };

  // Open the dropdown at the family in view
  const menu = document.querySelector('.family-bar-menu');
  if (bar && menu) {
    bar.addEventListener('shown.bs.dropdown', () => {
      const link = menu.querySelector('.active');
      if (link) menu.scrollTop = link.offsetTop - menu.clientHeight / 3;
    });
  }

  let pending = false;
  const schedule = () => {
    if (pending) return;
    pending = true;
    requestAnimationFrame(() => { pending = false; update(); });
  };
  window.addEventListener('scroll', schedule, {passive: true});
  window.addEventListener('resize', schedule);
  update();
});
