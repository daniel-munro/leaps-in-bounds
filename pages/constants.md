---
layout: default
title: Constants
permalink: /constants/
---

# Constants

{% for group in site.data.constant_groups %}
## {{ group[1].name }} {#{{ group.first }}}

{{ group[1].description }}

<p>Compilation status: {% case group[1].research_status %}
  {% when "initial" %}
    <span class="badge bg-warning" data-bs-toggle="tooltip" data-bs-placement="top" 
      title="Basic, incomplete information gathered">Initial</span>
  {% when "sourced" %}
    <span class="badge bg-info" data-bs-toggle="tooltip" data-bs-placement="top" 
      title="All current values and bounds are present and sourced">Sourced</span>
  {% when "thorough" %}
    <span class="badge bg-success" data-bs-toggle="tooltip" data-bs-placement="top" 
      title="Comprehensive research, all historical bounds updates that could be found are present and sourced">Thorough</span>
  {% else %}
    <span class="badge bg-secondary" data-bs-toggle="tooltip" data-bs-placement="top" 
      title="Compilation status not specified">Unknown</span>
{% endcase %}</p>

{% include constant_tables/{{ group.first }}.html %}
<br>
{% endfor %}
