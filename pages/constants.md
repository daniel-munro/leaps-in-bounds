---
layout: default
title: Constants
permalink: /constants/
---

# Constants

{% for group in site.data.constant_groups %}
## {{ group[1].group_name }}

{{ group[1].group_description }}

{% include constant_tables/{{ group.first }}.html %}
<br>
{% endfor %}
