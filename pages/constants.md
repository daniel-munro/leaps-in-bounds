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
    {% for category in site.data.categories %}
      <li>
        <h6 class="dropdown-header">{{ category.msc }} {{ category.name }}</h6>
      </li>
      {% for group_id in category.groups %}
        {% assign group = site.data.constant_groups[group_id] %}
        <li><a class="dropdown-item ps-4" href="#{{ group_id }}">{{ group.name }}</a></li>
      {% endfor %}
      {% unless forloop.last %}
        <li><hr class="dropdown-divider"></li>
      {% endunless %}
    {% endfor %}
  </ul>
</div>

{% for category in site.data.categories %}
<hr>
<h2 class="text-center">{{ category.msc }} {{ category.name }}</h2>

{% for group_id in category.groups %}
{% assign group = site.data.constant_groups[group_id] %}
### {{ group.name }} {#{{ group_id }}}

{% if group.representative_image %}
{% assign image_id = group.representative_image %}
{% assign image = site.data.constants[image_id].image %}
<div class="constant-group-image">
  <img src="{{ image.path }}" alt="{{ image.alt_text }}" data-bs-toggle="tooltip" data-bs-placement="top" title="{{ image.alt_text }}">
  <div class="image-credit">
    <span>{{ image.credit }}. {{ image.license }}.</span>
  </div>
</div>
{% endif %}

{{ group.description }}

{% if group.external_ids %}
  <p class="d-flex flex-wrap gap-2">
    {% if group.external_ids.wikipedia_en %}<a class="btn btn-outline-secondary btn-sm" href="https://en.wikipedia.org/wiki/{{ group.external_ids.wikipedia_en }}">Wikipedia</a>{% endif %}
    {% if group.external_ids.wikidata %}<a class="btn btn-outline-secondary btn-sm" href="https://www.wikidata.org/wiki/{{ group.external_ids.wikidata }}">Wikidata</a>{% endif %}
    {% if group.external_ids.mathworld %}<a class="btn btn-outline-secondary btn-sm" href="https://mathworld.wolfram.com/{{ group.external_ids.mathworld }}.html">MathWorld</a>{% endif %}
    {% if group.external_ids.metamath %}<a class="btn btn-outline-secondary btn-sm" href="http://us.metamath.org/mpeuni/{{ group.external_ids.metamath }}.html">Metamath</a>{% endif %}
    {% if group.external_ids.msc %}<a class="btn btn-outline-secondary btn-sm" href="https://mathscinet.ams.org/msc/msc2020.html?t={{ group.external_ids.msc }}">MSC2020</a>{% endif %}
    {% if group.external_ids.planetmath %}<a class="btn btn-outline-secondary btn-sm" href="https://planetmath.org/{{ group.external_ids.planetmath }}">PlanetMath</a>{% endif %}
    {% if group.external_ids.oeis %}<a class="btn btn-outline-secondary btn-sm" href="https://oeis.org/{{ group.external_ids.oeis }}">OEIS</a>{% endif %}
  </p>
{% endif %}

<p>Compilation status: {% case group.research_status %}
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

{% include constant_tables/{{ group_id }}.html %}
<br>
{% endfor %}

{% endfor %}
