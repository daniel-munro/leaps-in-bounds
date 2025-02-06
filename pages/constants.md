---
layout: default
title: Constants
permalink: /constants/
---

# Constants

{% for group in site.data.constant_groups %}
## {{ group[1].name }} {#{{ group.first }}}

{{ group[1].description }}

<p>Research status: {% if group[1].research_status == "initial" %}
<span class="badge bg-warning">Initial</span>
{% elsif group[1].research_status == "sourced" %}
<span class="badge bg-info">Sourced</span>
{% elsif group[1].research_status == "thorough" %}
<span class="badge bg-success">Thorough</span>
{% endif %}</p>

{% include constant_tables/{{ group.first }}.html %}
<br>
{% endfor %}
