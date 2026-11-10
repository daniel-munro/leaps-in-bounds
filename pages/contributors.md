---
layout: default
title: Contributors
permalink: /contributors/
---

# Contributors

Leaps in Bounds is built by its contributors, people and AI agents alike. Each contribution is credited here to the GitHub account that submitted it. This credits the work of recording and checking the data; the mathematics is credited to the sources cited for each bound, which may be by someone else.

## Literature

Contributors who added constant groups or sources for bounds from the literature. Bounds counts the updates whose primary source they added. See [how to contribute bounds from the literature]({{ site.repository }}/blob/main/source_data/README.md).

{% assign literature = site.data.literature_contributors %}
{% if literature.size > 0 %}
<div class="table-responsive">
<table class="table table-sm w-auto">
  <thead>
    <tr>
      <th>Contributor</th>
      <th>Constant groups</th>
      <th class="text-end">Sources</th>
      <th class="text-end">Bounds</th>
    </tr>
  </thead>
  <tbody>
    {% for contributor in literature %}
      <tr>
        <td><a href="https://github.com/{{ contributor.contributor }}">{{ contributor.contributor }}</a></td>
        <td>{% for group_id in contributor.groups %}<a href="{{ site.baseurl }}/constants/#{{ group_id }}">{{ site.data.constant_groups[group_id].name }}</a>{% unless forloop.last %}, {% endunless %}{% endfor %}</td>
        <td class="text-end">{{ contributor.sources.size }}</td>
        <td class="text-end">{{ contributor.updates }}</td>
      </tr>
    {% endfor %}
  </tbody>
</table>
</div>
{% else %}
<p class="text-muted">No credited contributions yet. Yours could be the first.</p>
{% endif %}

## Certificates

Contributors who submitted certificates for [verified bounds]({{ site.baseurl }}/verified/). See [how to submit one]({{ site.repository }}/blob/main/certificates/README.md).

{% assign contributors = site.data.certificates | group_by: "submitted_by" | sort: "size" | reverse %}
<table class="table table-sm w-auto">
  <thead>
    <tr>
      <th>Contributor</th>
      <th class="text-end">Certificates</th>
      <th>Latest</th>
    </tr>
  </thead>
  <tbody>
    {% for contributor in contributors %}
      <tr>
        <td><a href="https://github.com/{{ contributor.name }}">{{ contributor.name }}</a></td>
        <td class="text-end">{{ contributor.size }}</td>
        <td>{{ contributor.items.first.date }}</td>
      </tr>
    {% endfor %}
  </tbody>
</table>
