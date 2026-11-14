---
layout: default
title: Constants
permalink: /constants/
---

# Constants

<p class="text-muted small">
  Brackets in a cell's corner mark bounds whose best evidence is a certificate:
  <b>[</b> lower, <b>]</b> upper.
  <b class="verified-equal">Green</b> is a verified bound discovered in the literature,
  and <b class="verified-new">purple</b> one discovered by a certificate.
  <b class="attested">Yellow</b> is an attested bound, which someone else checked with a published checker but hasn't been checked here.
  <b class="verified-weaker">Gray</b> means only a weaker bound is verified.
  See the <a href="{{ site.baseurl }}/unverified/">bounds that aren't verified yet</a>.
</p>

<div class="dropdown mb-4">
  <button class="btn btn-secondary dropdown-toggle" type="button" id="familyDropdown" data-bs-toggle="dropdown" aria-expanded="false">
    Jump to family
  </button>
  <ul class="dropdown-menu" aria-labelledby="familyDropdown">
    {% for category in site.data.categories %}
      <li>
        <h6 class="dropdown-header">{{ category.msc }} {{ category.name }}</h6>
      </li>
      {% for family_id in category.families %}
        {% assign family = site.data.families[family_id] %}
        <li><a class="dropdown-item ps-4" href="#{{ family_id }}">{{ family.name }}</a></li>
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

{% for family_id in category.families %}
{% assign family = site.data.families[family_id] %}
### {{ family.name }} {#{{ family_id }}}

{% if family.representative_image %}
{% assign image_id = family.representative_image %}
{% assign image = site.data.constants[image_id].image %}
<div class="family-image">
  <img src="{{ image.path }}" alt="{{ image.alt_text }}" data-bs-toggle="tooltip" data-bs-placement="top" title="{{ image.alt_text }}">
  {% if image.credit %}
  <div class="image-credit">
    <span>{{ image.credit }}. {{ image.license }}.</span>
  </div>
  {% endif %}
</div>
{% endif %}

{{ family.description }}

{% if family.external_ids %}
  <p class="d-flex flex-wrap gap-2">
    {% if family.external_ids.wikipedia_en %}<a class="btn btn-outline-secondary btn-sm" href="https://en.wikipedia.org/wiki/{{ family.external_ids.wikipedia_en }}">Wikipedia</a>{% endif %}
    {% if family.external_ids.wikidata %}<a class="btn btn-outline-secondary btn-sm" href="https://www.wikidata.org/wiki/{{ family.external_ids.wikidata }}">Wikidata</a>{% endif %}
    {% if family.external_ids.mathworld %}<a class="btn btn-outline-secondary btn-sm" href="https://mathworld.wolfram.com/{{ family.external_ids.mathworld }}.html">MathWorld</a>{% endif %}
    {% if family.external_ids.metamath %}<a class="btn btn-outline-secondary btn-sm" href="http://us.metamath.org/mpeuni/{{ family.external_ids.metamath }}.html">Metamath</a>{% endif %}
    {% if family.external_ids.msc %}<a class="btn btn-outline-secondary btn-sm" href="https://mathscinet.ams.org/msc/msc2020.html?t={{ family.external_ids.msc }}">MSC2020</a>{% endif %}
    {% if family.external_ids.planetmath %}<a class="btn btn-outline-secondary btn-sm" href="https://planetmath.org/{{ family.external_ids.planetmath }}">PlanetMath</a>{% endif %}
    {% if family.external_ids.oeis %}<a class="btn btn-outline-secondary btn-sm" href="https://oeis.org/{{ family.external_ids.oeis }}">OEIS</a>{% endif %}
  </p>
{% endif %}

{% include constant_tables/{{ family_id }}.html %}
<br>
{% endfor %}

{% endfor %}

<script defer src="{{ site.baseurl }}/assets/js/constant_cards.js"></script>
