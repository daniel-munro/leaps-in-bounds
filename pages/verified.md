---
layout: default
title: Verified bounds
permalink: /verified/
---

# Verified bounds

Verified bounds come with a [certificate]({{ site.repository }}/blob/main/certificates/README.md) that is checked automatically: an explicit construction checked by a program, or a formal proof in Lean. Anyone can submit one, and each is credited to whoever submitted it. See the [unverified bounds]({{ site.baseurl }}/unverified/) for bounds from the literature that still need one.

All certificates are also available as [YAML]({{ site.baseurl }}/data/certificates.yml), [JSON]({{ site.baseurl }}/data/certificates.json), [CSV]({{ site.baseurl }}/data/certificates.csv) or [TSV]({{ site.baseurl }}/data/certificates.tsv).

{% assign certificates = site.data.certificates %}

## Contributors

{% assign contributors = certificates | group_by: "submitted_by" | sort: "size" | reverse %}
<table class="table table-sm w-auto">
  <thead>
    <tr>
      <th>Contributor</th>
      <th class="text-end">Certificates</th>
      <th class="text-end">Beyond the literature</th>
      <th>Latest</th>
    </tr>
  </thead>
  <tbody>
    {% for contributor in contributors %}
      {% assign new_rows = contributor.items | where: "comparison", "new" %}
      {% assign stronger_rows = contributor.items | where: "comparison", "stronger" %}
      <tr>
        <td><strong>{{ contributor.name }}</strong></td>
        <td class="text-end">{{ contributor.size }}</td>
        <td class="text-end">{{ new_rows.size | plus: stronger_rows.size }}</td>
        <td>{{ contributor.items.first.date }}</td>
      </tr>
    {% endfor %}
  </tbody>
</table>

<p class="text-muted small">Beyond the literature counts certificates for bounds that are stronger than, or absent from, the best bound in the literature.</p>

## Recent certificates

{% assign recent = certificates | slice: 0, 100 %}
<div class="table-responsive">
<table class="table table-sm small">
  <thead>
    <tr>
      <th>Date</th>
      <th>Contributor</th>
      <th>Constant</th>
      <th>Bound</th>
      <th>Evidence</th>
      <th>Compared with the literature</th>
    </tr>
  </thead>
  <tbody>
    {% for cert in recent %}
      {% assign constant = site.data.constants[cert.constant] %}
      {% if cert.bound == "lower" %}{% assign relation = "\ge" %}{% else %}{% assign relation = "\le" %}{% endif %}
      <tr>
        <td class="text-nowrap">{{ cert.date }}</td>
        <td><strong>{{ cert.submitted_by }}</strong></td>
        <td><a href="{{ site.baseurl }}/constants/{{ cert.constant }}">{{ constant.name }}</a></td>
        <td class="text-nowrap"><a href="{{ site.repository }}/blob/main/{{ cert.path }}">${{ relation }} {{ cert.value.latex }}$</a></td>
        <td>{% if cert.kind == "lean" %}Lean proof{% else %}Construction{% endif %}</td>
        <td>{% include certificate_comparison.html cert=cert %}</td>
      </tr>
    {% endfor %}
  </tbody>
</table>
</div>

{% if certificates.size > 100 %}
<p class="text-muted small">Showing the 100 most recent of {{ certificates.size }} certificates. The downloads above have all of them.</p>
{% endif %}
