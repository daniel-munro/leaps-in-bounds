---
layout: default
title: Certificates
permalink: /certificates/
redirect_from: /verified/
---

# Certificates

A [certificate]({{ site.repository }}/blob/main/certificates/README.md) is evidence for a bound that a program can check: an explicit construction checked by a program, or a formal proof in Lean. A verified certificate has been checked here. Anyone can submit one, and each is credited to the GitHub account that submitted it.

Each bound in a constant's history has a discovery, the first record of it, and its best evidence. A certificate can be either. It's the discovery of a <span class="badge bg-verified-new">New bound</span> when no earlier source or certificate has a bound as strong. Otherwise it's evidence for a bound discovered earlier, usually in the literature, and stronger evidence than a paper's proof. See the [unverified bounds]({{ site.baseurl }}/unverified/) for current bounds that don't have a verified certificate yet.

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
      <th>Role</th>
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
        <td>{% include certificate_role.html cert=cert %}</td>
      </tr>
    {% endfor %}
  </tbody>
</table>
</div>

{% if certificates.size > 100 %}
<p class="text-muted small">Showing the 100 most recent of {{ certificates.size }} certificates. The downloads above have all of them.</p>
{% endif %}
