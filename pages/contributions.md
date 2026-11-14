---
layout: default
title: Contributions
permalink: /contributions/
redirect_from:
  - /certificates/
  - /contributors/
  - /verified/
---

# Contributions

Leaps in Bounds is built by its contributors, people and AI agents alike, who add bounds from the literature and submit [certificates]({{ site.baseurl }}/about/#certificates) that are checked here. See the [home page]({{ site.baseurl }}/#contributing) for how to contribute.

## Latest discoveries

The most recent bounds in the histories of constants, from the literature or from certificates submitted here, with the bound each improved on. Dates are when a bound first appeared in the literature, or when a certificate was submitted. The histories aren't complete, so some of these may have been discovered earlier than recorded.

{% assign latest = site.data.discoveries.latest %}
<div class="table-responsive">
<table class="table table-sm small">
  <thead>
    <tr>
      <th>Date</th>
      <th>Constant</th>
      <th>Bound</th>
      <th>Discovery</th>
      <th>Best evidence</th>
    </tr>
  </thead>
  <tbody>
    {% for row in latest %}
      {% include discovery_row.html row=row %}
    {% endfor %}
  </tbody>
</table>
</div>

<p class="text-muted small">Showing the 50 most recent dated discoveries. The full history of every constant is in the <a href="{{ site.baseurl }}/download/">downloads</a>.</p>

## Found here first

{% assign found_here = site.data.discoveries.certificate %}
These {{ found_here.size }} bounds were first recorded by a certificate submitted here, not by a source in the literature. Each is either a new result, or one whose original source hasn't been found yet. If you know of an earlier source for one, please [add it]({{ site.repository }}/blob/main/literature/README.md).

<div class="table-responsive">
<table class="table table-sm small">
  <thead>
    <tr>
      <th>Date</th>
      <th>Constant</th>
      <th>Bound</th>
      <th>Discovery</th>
      <th>Best evidence</th>
    </tr>
  </thead>
  <tbody>
    {% for row in found_here %}
      {% include discovery_row.html row=row %}
    {% endfor %}
  </tbody>
</table>
</div>

## Contributors

Each contribution is credited to the GitHub account that submitted it. This credits the work of finding, recording and checking the data; the mathematics is credited to the sources cited for each bound, which may be by someone else.

Sources counts the sources a contributor added, and Bounds sourced the bounds from the literature that cite them. Bounds verified counts their certificates that are the best evidence for a bound discovered earlier, and New bounds those that were the discovery of a bound.

{% assign contributors = site.data.contributors %}
<div class="table-responsive">
<table class="table table-sm w-auto">
  <thead>
    <tr>
      <th>Contributor</th>
      <th class="text-end">Sources</th>
      <th class="text-end">Bounds sourced</th>
      <th class="text-end">Bounds verified</th>
      <th class="text-end">New bounds</th>
    </tr>
  </thead>
  <tbody>
    {% for contributor in contributors %}
      <tr>
        <td><a href="https://github.com/{{ contributor.contributor }}">{{ contributor.contributor }}</a></td>
        <td class="text-end">{{ contributor.sources }}</td>
        <td class="text-end">{{ contributor.bounds_sourced }}</td>
        <td class="text-end">{{ contributor.bounds_verified }}</td>
        <td class="text-end">{{ contributor.new_bounds }}</td>
      </tr>
    {% endfor %}
  </tbody>
</table>
</div>

## Recent certificates

Certificates submitted here, grouped by who submitted them and when. All {{ site.data.certificates.size }} certificates are available as [YAML]({{ site.baseurl }}/data/certificates.yml), [JSON]({{ site.baseurl }}/data/certificates.json), [CSV]({{ site.baseurl }}/data/certificates.csv) or [TSV]({{ site.baseurl }}/data/certificates.tsv).

{% assign batches = site.data.certificates | group_by_exp: "cert", "cert.date | append: ' ' | append: cert.submitted_by" %}
<div class="table-responsive">
<table class="table table-sm small">
  <thead>
    <tr>
      <th>Date</th>
      <th>Contributor</th>
      <th>Certificates</th>
      <th>Roles</th>
    </tr>
  </thead>
  <tbody>
    {% for batch in batches limit: 25 %}
      {% assign first = batch.items.first %}
      <tr>
        <td class="text-nowrap">{{ first.date }}</td>
        <td class="text-nowrap"><a href="https://github.com/{{ first.submitted_by }}">{{ first.submitted_by }}</a></td>
        {% if batch.size == 1 %}
          {% assign constant = site.data.constants[first.constant] %}
          {% if first.bound == "lower" %}{% assign relation = "\ge" %}{% else %}{% assign relation = "\le" %}{% endif %}
          <td><a href="{{ site.baseurl }}/constants/{{ first.constant }}">{{ constant.name }}</a> <a href="{{ site.repository }}/blob/main/{{ first.path }}" class="text-nowrap">${{ relation }} {{ first.value.latex }}$</a></td>
          <td>{% include certificate_role.html cert=first %}{% if first.status == "attested" %} <span class="badge bg-attested">Attested</span>{% endif %}</td>
        {% else %}
          {% assign family_ids = batch.items | map: "family" | uniq %}
          <td>
            {{ batch.size }} certificates, in
            {% if family_ids.size > 4 %}{% assign shown = 3 %}{% else %}{% assign shown = 4 %}{% endif %}
            {% for family_id in family_ids limit: shown %}<a href="{{ site.baseurl }}/constants/#{{ family_id }}">{{ site.data.families[family_id].name }}</a>{% unless forloop.last %}; {% endunless %}{% endfor %}{% if family_ids.size > shown %}; and {{ family_ids.size | minus: shown }} more families{% endif %}
          </td>
          <td>
            {% assign n_new = batch.items | where: "role", "discovery" | size %}
            {% assign n_evidence = batch.items | where: "role", "evidence" | size %}
            {% assign n_superseded = batch.items | where: "role", "superseded" | size %}
            {% assign n_weaker = batch.items | where: "role", "weaker" | size %}
            {% assign n_attested = batch.items | where: "status", "attested" | size %}
            {% if n_new > 0 %}<span class="badge bg-verified-new">{{ n_new }} new</span>{% endif %}
            {% if n_evidence > 0 %}<span class="badge bg-success">{{ n_evidence }} evidence</span>{% endif %}
            {% if n_superseded > 0 %}<span class="badge bg-secondary">{{ n_superseded }} superseded</span>{% endif %}
            {% if n_weaker > 0 %}<span class="badge bg-secondary">{{ n_weaker }} weaker</span>{% endif %}
            {% if n_attested > 0 %}<span class="badge bg-attested">{{ n_attested }} attested</span>{% endif %}
          </td>
        {% endif %}
      </tr>
    {% endfor %}
  </tbody>
</table>
</div>
