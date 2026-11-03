// Show a card with a constant's image and bounds on hovering (or focusing) it
// in a table. On touch screens, a tap opens the constant's page as before.
document.addEventListener('DOMContentLoaded', () => {
  if (!window.matchMedia('(hover: hover) and (pointer: fine)').matches) return;

  // Cards for all constants, fetched the first time one is needed
  let cards = null;
  const loadCards = () => cards ??= fetch('/assets/generated/constant_cards.json').then(r => r.json());

  for (const link of document.querySelectorAll('a.cell-link, a.constant-box')) {
    const id = link.getAttribute('href').split('/').filter(Boolean).pop();
    let popover = null;
    let timer = null;

    const show = async () => {
      const html = (await loadCards())[id];
      if (timer === null || !html) return;  // Left before the cards loaded
      if (popover === null) {
        const content = document.createElement('div');
        content.innerHTML = html;
        renderMathInElement(content, {delimiters: [{left: '$', right: '$', display: false}]});
        popover = new bootstrap.Popover(link, {
          trigger: 'manual',
          html: true,
          sanitize: false,
          content,
          placement: 'auto',
          customClass: 'constant-card-popover',
        });
      }
      popover.show();
    };
    // A short delay so moving the mouse across the table doesn't flash cards
    const start = () => { timer = setTimeout(show, 150); };
    const stop = () => {
      clearTimeout(timer);
      timer = null;
      popover?.hide();
    };

    link.addEventListener('mouseenter', start);
    link.addEventListener('mouseleave', stop);
    link.addEventListener('focus', start);
    link.addEventListener('blur', stop);
  }
});
