---
layout: default
title: Unverified bounds
permalink: /unverified/
---

# Unverified bounds

These are the current bounds whose best evidence isn't a verified [certificate]({{ site.repository }}/blob/main/certificates/README.md) yet, for the families of constants that accept them. Most come from the literature, and each is a chance to give a published bound evidence checked here.

Some bounds are <span class="badge bg-attested">Attested</span>: a certificate has the evidence, and someone else says they checked it with a published checker, but checking it here has been too slow so far. Running their checker yourself doesn't make it verified, since that's one more attestation. What helps is making the check fast enough to run here: a faster checker for the family, a smaller witness for the same bound, or a Lean proof.

A <span class="badge bg-success">Witness</span> bound can be certified by giving the construction itself, which is often in the cited source or its ancillary files. A <span class="badge bg-secondary">Lean proof</span> bound needs a formal proof that no better construction exists, which is usually much harder.

This list is also available as [YAML]({{ site.baseurl }}/data/unverified_bounds.yml), [JSON]({{ site.baseurl }}/data/unverified_bounds.json), [CSV]({{ site.baseurl }}/data/unverified_bounds.csv) or [TSV]({{ site.baseurl }}/data/unverified_bounds.tsv).

{% assign all_rows = site.data.unverified_bounds %}

<table class="table table-sm table-bordered w-auto">
  <thead>
    <tr>
      <th>Family</th>
      <th class="text-end">Witness</th>
      <th class="text-end">Lean proof</th>
    </tr>
  </thead>
  <tbody>
    {% for category in site.data.categories %}
      {% for family_id in category.families %}
        {% assign rows = all_rows | where: "family", family_id %}
        {% if rows.size > 0 %}
          {% assign witness_rows = rows | where: "certify_with", "witness" %}
          {% assign lean_rows = rows | where: "certify_with", "lean" %}
          <tr>
            <td><a href="#{{ family_id }}">{{ site.data.families[family_id].name }}</a></td>
            <td class="text-end">{{ witness_rows.size }}</td>
            <td class="text-end">{{ lean_rows.size }}</td>
          </tr>
        {% endif %}
      {% endfor %}
    {% endfor %}
  </tbody>
</table>

{% for category in site.data.categories %}
{% for family_id in category.families %}
{% assign rows = all_rows | where: "family", family_id %}
{% if rows.size > 0 %}
{% assign witness_rows = rows | where: "certify_with", "witness" %}
{% assign lean_rows = rows | where: "certify_with", "lean" %}
{% assign ordered_rows = witness_rows | concat: lean_rows %}

<h2 id="{{ family_id }}" class="h4 mt-5">{{ site.data.families[family_id].name }}</h2>

<div class="table-responsive">
<table class="table table-sm small">
  <thead>
    <tr>
      <th>Constant</th>
      <th>Bound</th>
      <th>Best evidence</th>
      <th>Verified</th>
      <th>Certify with</th>
      <th>Discovery</th>
    </tr>
  </thead>
  <tbody>
    {% for row in ordered_rows %}
      {% assign constant = site.data.constants[row.constant] %}
      {% if row.bound == "lower" %}{% assign relation = "\ge" %}{% else %}{% assign relation = "\le" %}{% endif %}
      <tr>
        <td><a href="{{ site.baseurl }}/constants/{{ row.constant }}">{{ constant.name }}</a></td>
        <td class="text-nowrap">${{ relation }} {{ row.value.latex }}$</td>
        <td>
          {% if row.evidence == "attested" %}
            {% assign attested_cert = constant.certificates | where: "id", row.evidence_certificate | first %}
            <a href="{{ attested_cert.attestation.checker }}"><span class="badge bg-attested">Attested</span></a>
          {% else %}
            <span class="badge text-bg-light border">Literature</span>
          {% endif %}
        </td>
        <td class="text-nowrap">
          {% if row.verified %}
            ${{ relation }} {{ row.verified.latex }}$
          {% else %}
            <span class="text-muted">none</span>
          {% endif %}
        </td>
        <td>
          {% if row.certify_with == "witness" %}
            <span class="badge bg-success">Witness</span>
          {% else %}
            <span class="badge bg-secondary">Lean proof</span>
          {% endif %}
        </td>
        <td>
          {% if row.discovery_kind == "certificate" %}
            {% assign cert = constant.certificates | where: "id", row.discovery | first %}
            {% include record_link.html certificate=cert %}
          {% elsif row.discovery %}
            {% include record_link.html source=row.discovery %}
          {% elsif row.via %}
            via {% include record_link.html source=row.via %}
          {% endif %}
        </td>
      </tr>
    {% endfor %}
  </tbody>
</table>
</div>
{% endif %}
{% endfor %}
{% endfor %}
