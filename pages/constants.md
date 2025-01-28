---
layout: default
title: Constants
permalink: /constants/
---

# Constants

<div class="constants-list">
  {% for constant in site.data.constants %}
    <div class="constant-entry">
      <h2><a href="{{ site.baseurl }}/constants/{{ constant[0] }}">{{ constant[1].name }}</a></h2>
      <p>{{ constant[1].description }}</p>
    </div>
  {% endfor %}
</div>
