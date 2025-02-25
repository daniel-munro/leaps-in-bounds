---
layout: default
title: Constants
permalink: /constants/
---

# Constants

<div class="dropdown mb-4">
  <button class="btn btn-secondary dropdown-toggle" type="button" id="groupDropdown" data-bs-toggle="dropdown" aria-expanded="false">
    Jump to group
  </button>
  <ul class="dropdown-menu" aria-labelledby="groupDropdown">
    {% for group in site.data.constant_groups %}
      <li><a class="dropdown-item" href="#{{ group.first }}">{{ group[1].name }}</a></li>
    {% endfor %}
  </ul>
</div>


{% for group in site.data.constant_groups %}
## {{ group[1].name }} {#{{ group.first }}}

{{ group[1].description }}

{% if group[1].external_ids %}
  <p class="d-flex flex-wrap gap-2">
    {% if group[1].external_ids.wikipedia_en %}<a class="btn btn-outline-secondary btn-sm" href="https://en.wikipedia.org/wiki/{{ group[1].external_ids.wikipedia_en }}">Wikipedia</a>{% endif %}
    {% if group[1].external_ids.wikidata %}<a class="btn btn-outline-secondary btn-sm" href="https://www.wikidata.org/wiki/{{ group[1].external_ids.wikidata }}">Wikidata</a>{% endif %}
    {% if group[1].external_ids.mathworld %}<a class="btn btn-outline-secondary btn-sm" href="https://mathworld.wolfram.com/{{ group[1].external_ids.mathworld }}.html">MathWorld</a>{% endif %}
    {% if group[1].external_ids.metamath %}<a class="btn btn-outline-secondary btn-sm" href="http://us.metamath.org/mpeuni/{{ group[1].external_ids.metamath }}.html">Metamath</a>{% endif %}
    {% if group[1].external_ids.msc %}<a class="btn btn-outline-secondary btn-sm" href="https://mathscinet.ams.org/msc/msc2020.html?t={{ group[1].external_ids.msc }}">MSC2020</a>{% endif %}
    {% if group[1].external_ids.planetmath %}<a class="btn btn-outline-secondary btn-sm" href="https://planetmath.org/{{ group[1].external_ids.planetmath }}">PlanetMath</a>{% endif %}
    {% if group[1].external_ids.oeis %}<a class="btn btn-outline-secondary btn-sm" href="https://oeis.org/{{ group[1].external_ids.oeis }}">OEIS</a>{% endif %}
  </p>
{% endif %}

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
