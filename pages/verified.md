---
layout: default
title: Verified bounds
permalink: /verified/
---

# Verified bounds

Verified bounds come with a [certificate]({{ site.repository }}/blob/main/certificates/README.md) whose evidence has been checked here: an explicit construction checked by a program, or a formal proof in Lean. Anyone can submit one, and each is credited to the GitHub account that submitted it, which may not be whoever found the bound. See the [unverified bounds]({{ site.baseurl }}/unverified/) for bounds from the literature that still need one.

Some certificates are <span class="badge bg-attested">Attested</span> instead: their evidence is too slow to check here so far, or too large to keep here, and someone else says they checked it with a checker they published. Anyone can run that checker on the evidence, but until it's checked here, an attested bound isn't verified.

All certificates are also available as [YAML]({{ site.baseurl }}/data/certificates.yml), [JSON]({{ site.baseurl }}/data/certificates.json), [CSV]({{ site.baseurl }}/data/certificates.csv) or [TSV]({{ site.baseurl }}/data/certificates.tsv).

{% assign certificates = site.data.certificates %}

See the [contributors]({{ site.baseurl }}/contributors/) of certificates and other data.

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
        <td><a href="https://github.com/{{ cert.submitted_by }}">{{ cert.submitted_by }}</a></td>
        <td><a href="{{ site.baseurl }}/constants/{{ cert.constant }}">{{ constant.name }}</a></td>
        <td class="text-nowrap"><a href="{{ site.repository }}/blob/main/{{ cert.path }}">${{ relation }} {{ cert.value.latex }}$</a></td>
        <td>{% if cert.kind == "lean" %}Lean proof{% else %}Construction{% endif %}{% if cert.status == "attested" %} <span class="badge bg-attested">Attested</span>{% endif %}</td>
        <td>{% include certificate_comparison.html cert=cert %}</td>
      </tr>
    {% endfor %}
  </tbody>
</table>
</div>

{% if certificates.size > 100 %}
<p class="text-muted small">Showing the 100 most recent of {{ certificates.size }} certificates. The downloads above have all of them.</p>
{% endif %}
