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

def verified_mark(const: Mapping[str, Any], side: str) -> str:
    """Generate a check mark noting that a constant's lower or upper bound is
    verified, highlighted if it's stronger than (or absent from) the
    literature."""
    source = const[f'{side}_bound_source']
    if source not in ('verified', 'both'):
        return ''
    title = f"Verified {side} bound by certificate {const[f'verified_{side}_certificate']}"
    css_class = 'verified-mark'
    if source == 'verified':
        css_class += ' verified-new'
        literature = const[f'literature_{side}_bound']
        if literature is None:
            title += '; none in the literature'
        else:
            title += f"; the literature has {literature['latex']}"
    return f'<span class="{css_class}" data-bs-toggle="tooltip" data-bs-placement="top" title="{title}">✓</span>'

def cell_content(const: Mapping[str, Any]) -> tuple[str, str]:
    """Generate the displayed value or bounds for a constant, with marks on
    verified values, and the CSS class for how well it's known."""
    if const['exact_value'] is not None:
        # Lower and upper marks stacked beside the value, in the same order as bounds
        marks = (
            f'<span class="exact-marks"><span>{verified_mark(const, "lower")}</span>'
            f'<span>{verified_mark(const, "upper")}</span></span>'
        )
        return f'<span>{html_for_value(const["exact_value"])}{marks}</span>', 'value-exact'

    # Keep each mark on the same line as its value (sequence boxes stack children)
    lb = f'<span>{html_for_value(const["lower_bound"])}{verified_mark(const, "lower")}</span>'
    ub = f'<span>{html_for_value(const["upper_bound"])}{verified_mark(const, "upper")}</span>'
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
