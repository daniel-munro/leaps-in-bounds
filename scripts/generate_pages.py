"""Generate constant page templates, constant tables, and the hover cards
shown for constants in the tables."""

import json
import os
import yaml
from html import escape
from typing import Any, Mapping

def html_for_value(value: Mapping[str, Any] | None) -> str:
    """Generate HTML for a value (details like alt_display are in its card)."""
    if value is None:
        return '$?$'
    return f'${value["latex"]}$'

def last_event(const: Mapping[str, Any], side: str) -> Mapping[str, Any] | None:
    """The latest bound on one side of a constant's history, if any."""
    events = [e for e in const['history'] if e['type'] == f'{side}_bound']
    return events[-1] if events else None

def verified_bracket(const: Mapping[str, Any], side: str) -> str:
    """Generate a bracket for the evidence of a constant's lower ([) or upper
    (]) bound: green if it's verified and was discovered in the literature,
    purple if it's verified and was discovered by a certificate, yellow if
    it's attested, and gray if only a weaker bound is verified."""
    bracket = '[' if side == 'lower' else ']'
    event = last_event(const, side)
    tier = event['evidence']['tier'] if event else None
    if tier == 'attested':
        label = (f"{side.capitalize()} bound {event['value']['latex']} attested by certificate "
                 f"{event['evidence']['certificate']}, checked elsewhere but not here")
        return f'<span class="attested" aria-label="{label}">{bracket}</span>'
    if tier == 'verified':
        new = event['discovery']['kind'] == 'certificate'
        label = f"{side.capitalize()} bound {event['value']['latex']} verified by certificate {event['evidence']['certificate']}"
        label += '; discovered by that certificate' if new else '; discovered in the literature'
        return f'<span class="{"verified-new" if new else "verified-equal"}" aria-label="{label}">{bracket}</span>'
    verified = const[f'verified_{side}_bound']
    if verified is None:
        return '<span></span>'  # Keep the other bracket in its slot
    label = (f"Weaker {side} bound {verified['latex']} verified by certificate "
             f"{const[f'verified_{side}_certificate']}; the current bound isn't verified")
    return f'<span class="verified-weaker" aria-label="{label}">{bracket}</span>'

def verified_brackets(const: Mapping[str, Any]) -> str:
    """Generate the brackets in a cell's corner for its verified bounds."""
    if all(const[f'{side}_bound_evidence'] in (None, 'literature') and const[f'verified_{side}_bound'] is None
           for side in ['lower', 'upper']):
        return ''
    return (
        f'<span class="verified-brackets">{verified_bracket(const, "lower")}'
        f'{verified_bracket(const, "upper")}</span>'
    )

def cell_content(const: Mapping[str, Any]) -> tuple[str, str]:
    """Generate the displayed value or bounds for a constant, with brackets
    for verified bounds, and the CSS class for how well it's known."""
    brackets = verified_brackets(const)
    if const['exact_value'] is not None:
        return f'<span>{html_for_value(const["exact_value"])}</span>{brackets}', 'value-exact'

    lb = f'<span>{html_for_value(const["lower_bound"])}</span>'
    ub = f'<span>{html_for_value(const["upper_bound"])}</span>'
    if const['lower_bound'] is None and const['upper_bound'] is None:
        css_class = 'value-unbounded'
    elif const['lower_bound'] is None or const['upper_bound'] is None:
        css_class = 'value-half-bounded'
    else:
        css_class = 'value-bounded'
    return f"{lb}<br>{ub}{brackets}", css_class

def generate_grid_html(
    family: Mapping[str, Any],
    constants: Mapping[str, Mapping[str, Any]],
) -> str:
    """Generate HTML table for a family with two parameters."""
    param1, param2 = family['parameters']
    rows = family['display_rows']
    cols = family['display_columns']
    
    html = [
        '<div class="table-responsive">',
        '  <table class="table table-bordered border-secondary-subtle align-middle constant-grid w-auto">',
        '    <thead>',
        f'      <tr><th scope="col">{param1}\\{param2}</th>'
    ]
    
    # Column headers
    for col in cols:
        html.append(f'        <th scope="col">{col}</th>')
    html.append('      </tr>')
    html.append('    </thead>')
    html.append('    <tbody>')
    
    # Table cells
    for r in rows:
        html.append(f'      <tr><th scope="row">{r}</th>')
        for c in cols:
            const_id = family['id_template'].format(**{param1: r, param2: c})
            
            if const_id not in constants:
                html.append('        <td class="table-secondary"></td>')
                continue
                
            content, cell_class = cell_content(constants[const_id])
            # The link fills the cell and centers its content in one block
            html.append(
                f'        <td class="constant-cell {cell_class}"><a href="/constants/{const_id}" '
                f'class="cell-link"><div>{content}</div></a></td>'
            )
        html.append('      </tr>')
    
    html.extend([
        '    </tbody>',
        '  </table>',
        '</div>'
    ])
    
    return '\n'.join(html) + '\n'

def generate_sequence_html(
    family: Mapping[str, Any],
    constants: Mapping[str, Mapping[str, Any]],
) -> str:
    """Generate HTML for a family with one parameter."""
    param = family['parameters'][0]
    values = []
    value_specs = family['parameter_values']
    for spec in value_specs:
        assert isinstance(spec, list) and len(spec) == 1 # Only one parameter
        spec = spec[0]
        if isinstance(spec, list):
            assert len(spec) == 2
            values.extend(list(range(spec[0], spec[1] + 1)))
        else:
            values.append(spec)

    html = ['<div class="constant-sequence">']

    for v in values:
        const_id = family['id_template'].format(**{param: v})
        
        if const_id not in constants:
            continue
            
        content, box_class = cell_content(constants[const_id])
        html.append(
            f'  <a href="/constants/{const_id}" class="constant-box {box_class}">'
            f'<strong>{v}</strong><br><div class="constant-box-values">{content}</div></a>'
        )

    html.append('</div>')
    return '\n'.join(html) + '\n'

def generate_single_html(
    family: Mapping[str, Any],
    constants: Mapping[str, Mapping[str, Any]],
) -> str:
    """Generate HTML for a family with no parameters."""
    html = ['<div class="constant-sequence">']
    
    content, box_class = cell_content(constants[family['id']])
    html.append(
        f'  <a href="/constants/{family["id"]}" class="constant-box {box_class}">'
        f'<div class="constant-box-values">{content}</div></a>'
    )

    html.append('</div>')
    return '\n'.join(html) + '\n'

def card_value(value: Mapping[str, Any]) -> str:
    """Generate card HTML for a value, with its alternative display if any."""
    html = f'${escape(value["latex"])}$'
    if value.get('alt_display') is not None:
        html += f' <span class="text-muted">({escape(str(value["alt_display"]))})</span>'
    return html

def card_reference(
    const: Mapping[str, Any],
    side: str,
    sources: Mapping[str, Mapping[str, Any]],
) -> str:
    """Generate card HTML for where a constant's lower or upper bound was
    discovered: a source, or a certificate."""
    event = last_event(const, side)
    if event is None:
        return ''
    discovery = event['discovery']
    if discovery['kind'] == 'certificate':
        reference = f"Certificate submitted by {discovery['submitted_by']}"
    elif discovery['id']:
        reference = sources[discovery['id']]['string']
    elif discovery['via']:
        reference = f"via {sources[discovery['via']]['string']}"
    else:
        reference = 'Reference unknown'
    date = f'{event["date"]}, ' if event.get('date') else ''
    return f'<div class="constant-card-source">{escape(date)}{escape(reference)}</div>'

def card_verification(const: Mapping[str, Any], side: str) -> str:
    """Generate card HTML for the best evidence for a constant's lower or
    upper bound, if it's a certificate, colored like its bracket, or for the
    strongest verified bound if it's weaker."""
    event = last_event(const, side)
    if event is None:
        return ''
    evidence = event['evidence']
    kind = 'Lean proof' if evidence['kind'] == 'lean' else 'checked construction'
    implied = (f" (via {card_value(evidence['value'])})" if evidence['value'] is not None else '')
    if evidence['tier'] == 'attested':
        certificate = next(c for c in const['certificates'] if c['id'] == evidence['certificate'])
        return (f'<div><span class="attested">✓</span> Attested{implied} by '
                f'{escape(certificate["attestation"]["by"])}, checked elsewhere</div>')
    if evidence['tier'] == 'verified':
        css_class = 'verified-new' if event['discovery']['kind'] == 'certificate' else 'verified-equal'
        return f'<div><span class="{css_class}">✓</span> Verified by {kind}{implied}</div>'
    verified = const[f'verified_{side}_bound']
    if verified is None:
        return ''
    certificate = next(c for c in const['certificates'] if c['id'] == const[f'verified_{side}_certificate'])
    kind = 'Lean proof' if certificate['kind'] == 'lean' else 'checked construction'
    return f'<div><span class="verified-weaker">✓</span> Verified {card_value(verified)} by {kind}</div>'

def generate_card_html(
    const: Mapping[str, Any],
    sources: Mapping[str, Mapping[str, Any]],
) -> str:
    """Generate the hover card for a constant: its image, name, value or bounds,
    and where they come from."""
    html = ['<div class="constant-card">', '<div class="constant-card-head">']
    if const.get('image'):
        html.append(f'<img src="{escape(const["image"]["path"])}" alt="{escape(const["image"]["alt_text"])}">')
    html.append(f'<div class="constant-card-name">{escape(const["name"])}')
    if const['exact_value'] is not None:
        html.append(f'<div class="constant-card-value">= {card_value(const["exact_value"])}</div>')
    html.extend(['</div>', '</div>', '<dl class="constant-card-bounds">'])

    references = {side: card_reference(const, side, sources) for side in ('lower', 'upper')}
    rows = []
    if const['exact_value'] is not None and references['lower'] == references['upper']:
        # Often one paper settles both bounds, so name it once
        rows.append(('Source', references['lower']))
        references = {'lower': '', 'upper': ''}
    for side in ('lower', 'upper'):
        if const['exact_value'] is not None:
            # The value is in the head, so just say where each bound comes from
            value = ''
        elif const[f'{side}_bound'] is None:
            value = '<div class="text-muted">Unknown</div>'
        else:
            value = f'<div>{card_value(const[f"{side}_bound"])}</div>'
        rows.append((side.capitalize(), value + references[side] + card_verification(const, side)))
    for label, content in rows:
        if content:
            html.append(f'<dt>{label}</dt><dd>{content}</dd>')
    html.extend(['</dl>', '</div>'])
    return ''.join(html)

with open("_data/constants.yml", "r") as file:
    constants = yaml.safe_load(file)

with open("_data/sources.yml", "r") as file:
    sources = yaml.safe_load(file)

# Hover cards, loaded by the constants page when first needed
os.makedirs("assets/generated", exist_ok=True)
with open("assets/generated/constant_cards.json", "w") as file:
    json.dump({id: generate_card_html(constant, sources) for id, constant in constants.items()}, file)

os.makedirs("pages/constants", exist_ok=True)

for id, constant in constants.items():
    fname = f"pages/constants/{id}.md"
    with open(fname, "w") as file:
        file.write("---\n")
        file.write("layout: constant\n")
        file.write(f"title: {constant['name']}\n")
        file.write(f"permalink: /constants/{id}/\n")
        file.write(f"id: {id}\n")
        file.write("---\n")

with open("_data/families.yml", "r") as file:
    families = yaml.safe_load(file)

os.makedirs("_includes/constant_tables", exist_ok=True)

for id, family in families.items():
    if family['display_type'] == 'grid':
        html = generate_grid_html(family, constants)
    elif family['display_type'] == 'sequence':
        html = generate_sequence_html(family, constants)
    elif family['display_type'] == 'single':
        family['id'] = id
        html = generate_single_html(family, constants)
    else:
        raise ValueError(f"Unknown display type: {family['display_type']}")
    with open(f"_includes/constant_tables/{id}.html", "w") as file:
        file.write(html)
