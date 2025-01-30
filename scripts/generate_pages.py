"""Generate constant page templates and constant tables."""

import os
import yaml

def generate_grid_html(group: dict, constants: dict) -> str:
    """Generate HTML table for a constant group with two parameters."""
    param1, param2 = group['parameters']
    rows = group['display_rows']
    cols = group['display_columns']
    
    html = [
        '<div class="table-responsive">',
        '  <table class="table table-bordered border-secondary-subtle constant-grid">',
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
                
            const = constants[const_id]
            if const['value'] is not None:
                cell_content = str(const['value'])
                cell_class = ' class="table-success"'
            else:
                lb = const['lower_bound'] if const['lower_bound'] is not None else '?'
                ub = const['upper_bound'] if const['upper_bound'] is not None else '?'
                cell_content = f"{lb} - {ub}"
                cell_class = ''
                
            html.append(
                f'        <td{cell_class}><a href="/constants/{const_id}" '
                f'class="cell-link">{cell_content}</a></td>'
            )
        html.append('      </tr>')
    
    html.extend([
        '    </tbody>',
        '  </table>',
        '</div>'
    ])
    
    return '\n'.join(html) + '\n'

def generate_sequence_html(group: dict, constants: dict) -> str:
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
            
        const = constants[const_id]
        if const['value'] is not None:
            content = str(const['value'])
            box_class = ' box-exact'
        else:
            lb = const['lower_bound'] if const['lower_bound'] is not None else '?'
            ub = const['upper_bound'] if const['upper_bound'] is not None else '?'
            content = f"{lb} - {ub}"
            box_class = ''
            
        html.append(
            f'  <a href="/constants/{const_id}" class="constant-box{box_class}">'
            f'<strong>{v}</strong>: {content}'
            f'  </a>'
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
    else:
        raise ValueError(f"Unknown display type: {group['display_type']}")
    with open(f"_includes/constant_tables/{id}.html", "w") as file:
        file.write(html)
