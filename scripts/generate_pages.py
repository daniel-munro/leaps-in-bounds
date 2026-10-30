"""Generate constant page templates and constant tables."""

import os
import yaml
from typing import Any, Mapping

def html_for_value(value: Mapping[str, Any] | None) -> str:
    """Generate HTML for a value, including an optional tooltip."""
    if value is None:
        return '$?$'
    html = f'${value["latex"]}$'
    if value.get('alt_display') is not None:
        html = f'<span data-bs-toggle="tooltip" data-bs-placement="top" title="{value["alt_display"]}">{html}</span>'
    return html

def verified_mark(const: Mapping[str, Any], sides: list[str]) -> str:
    """Generate a check mark noting that a displayed value is verified on the
    given sides, highlighted if it's stronger than (or absent from) the
    literature."""
    sides = [side for side in sides if const[f'{side}_bound_source'] in ('verified', 'both')]
    if not sides:
        return ''
    notes = []
    for side in sides:
        note = f"Verified {side} bound by certificate {const[f'verified_{side}_certificate']}"
        if const[f'{side}_bound_source'] == 'verified':
            literature = const[f'literature_{side}_bound']
            if literature is None:
                note += '; none in the literature'
            else:
                note += f"; the literature has {literature['latex']}"
        notes.append(note)
    new = any(const[f'{side}_bound_source'] == 'verified' for side in sides)
    css_class = 'verified-mark verified-new' if new else 'verified-mark'
    title = '. '.join(notes)
    return f'<span class="{css_class}" data-bs-toggle="tooltip" data-bs-placement="top" title="{title}">✓</span>'

def cell_content(const: Mapping[str, Any]) -> tuple[str, str]:
    """Generate the displayed value or bounds for a constant, with marks on
    verified values, and the CSS class for how well it's known."""
    def marked(value: Mapping[str, Any] | None, sides: list[str]) -> str:
        # Keep the mark on the same line as its value (sequence boxes stack children)
        return f'<span>{html_for_value(value)}{verified_mark(const, sides)}</span>'

    if const['exact_value'] is not None:
        return marked(const['exact_value'], ['lower', 'upper']), 'value-exact'
    lb = marked(const['lower_bound'], ['lower'])
    ub = marked(const['upper_bound'], ['upper'])
    if const['lower_bound'] is None and const['upper_bound'] is None:
        css_class = 'value-unbounded'
    elif const['lower_bound'] is None or const['upper_bound'] is None:
        css_class = 'value-half-bounded'
    else:
        css_class = 'value-bounded'
    return f"{lb}<br>{ub}", css_class

def generate_grid_html(
    group: Mapping[str, Any],
    constants: Mapping[str, Mapping[str, Any]],
) -> str:
    """Generate HTML table for a constant group with two parameters."""
    param1, param2 = group['parameters']
    rows = group['display_rows']
    cols = group['display_columns']
    
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
            const_id = group['id_template'].format(**{param1: r, param2: c})
            
            if const_id not in constants:
                html.append('        <td class="table-secondary"></td>')
                continue
                
            content, cell_class = cell_content(constants[const_id])
            html.append(
                f'        <td class="constant-cell {cell_class}"><a href="/constants/{const_id}" '
                f'class="cell-link">{content}</a></td>'
            )
        html.append('      </tr>')
    
    html.extend([
        '    </tbody>',
        '  </table>',
        '</div>'
    ])
    
    return '\n'.join(html) + '\n'

def generate_sequence_html(
    group: Mapping[str, Any],
    constants: Mapping[str, Mapping[str, Any]],
) -> str:
    """Generate HTML for a constant group with one parameter."""
    param = group['parameters'][0]
    values = []
    value_specs = group['parameter_values']
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
        const_id = group['id_template'].format(**{param: v})
        
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
    group: Mapping[str, Any],
    constants: Mapping[str, Mapping[str, Any]],
) -> str:
    """Generate HTML for a constant group with no parameters."""
    html = ['<div class="constant-sequence">']
    
    content, box_class = cell_content(constants[group['id']])
    html.append(
        f'  <a href="/constants/{group["id"]}" class="constant-box {box_class}">'
        f'<div class="constant-box-values">{content}</div></a>'
    )

    html.append('</div>')
    return '\n'.join(html) + '\n'

with open("_data/constants.yml", "r") as file:
    constants = yaml.safe_load(file)

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

with open("_data/constant_groups.yml", "r") as file:
    constant_groups = yaml.safe_load(file)

os.makedirs("_includes/constant_tables", exist_ok=True)

for id, group in constant_groups.items():
    if group['display_type'] == 'grid':
        html = generate_grid_html(group, constants)
    elif group['display_type'] == 'sequence':
        html = generate_sequence_html(group, constants)
    elif group['display_type'] == 'single':
        group['id'] = id
        html = generate_single_html(group, constants)
    else:
        raise ValueError(f"Unknown display type: {group['display_type']}")
    with open(f"_includes/constant_tables/{id}.html", "w") as file:
        file.write(html)
