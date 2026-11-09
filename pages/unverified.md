---
layout: default
title: Unverified bounds
permalink: /unverified/
---

# Unverified bounds

These are the best bounds from the literature that no verified certificate matches yet, for the families of constants that accept [certificates]({{ site.repository }}/blob/main/certificates/README.md). Each one is a chance to turn a published bound into a verified one.

Some bounds are <span class="badge bg-attested">Attested</span>: a certificate has the evidence, and someone else says they checked it with a published checker, but checking it here has been too slow so far. Running their checker yourself doesn't make it verified, since that's one more attestation. What helps is making the check fast enough to run here: a faster checker for the family, a smaller witness for the same bound, or a Lean proof.

A <span class="badge bg-success">Witness</span> bound can be certified by giving the construction itself, which is often in the cited source or its ancillary files. A <span class="badge bg-secondary">Lean proof</span> bound needs a formal proof that no better construction exists, which is usually much harder.

This list is also available as [YAML]({{ site.baseurl }}/data/unverified_bounds.yml), [JSON]({{ site.baseurl }}/data/unverified_bounds.json), [CSV]({{ site.baseurl }}/data/unverified_bounds.csv) or [TSV]({{ site.baseurl }}/data/unverified_bounds.tsv).

{% assign all_rows = site.data.unverified_bounds %}

<table class="table table-sm table-bordered w-auto">
  <thead>
    <tr>
      <th>Group</th>
      <th class="text-end">Witness</th>
      <th class="text-end">Lean proof</th>
    </tr>
  </thead>
  <tbody>
    {% for category in site.data.categories %}
      {% for group_id in category.groups %}
        {% assign rows = all_rows | where: "group", group_id %}
        {% if rows.size > 0 %}
          {% assign witness_rows = rows | where: "evidence", "witness" %}
          {% assign lean_rows = rows | where: "evidence", "lean" %}
          <tr>
            <td><a href="#{{ group_id }}">{{ site.data.constant_groups[group_id].name }}</a></td>
            <td class="text-end">{{ witness_rows.size }}</td>
            <td class="text-end">{{ lean_rows.size }}</td>
          </tr>
        {% endif %}
      {% endfor %}
    {% endfor %}
  </tbody>
</table>

{% for category in site.data.categories %}
{% for group_id in category.groups %}
{% assign rows = all_rows | where: "group", group_id %}
{% if rows.size > 0 %}
{% assign witness_rows = rows | where: "evidence", "witness" %}
{% assign lean_rows = rows | where: "evidence", "lean" %}
{% assign ordered_rows = witness_rows | concat: lean_rows %}

<h2 id="{{ group_id }}" class="h4 mt-5">{{ site.data.constant_groups[group_id].name }}</h2>

<div class="table-responsive">
<table class="table table-sm small">
  <thead>
    <tr>
      <th>Constant</th>
      <th>Literature</th>
      <th>Attested</th>
      <th>Verified</th>
      <th>Evidence</th>
      <th>Source</th>
    </tr>
  </thead>
  <tbody>
    {% for row in ordered_rows %}
      {% assign constant = site.data.constants[row.constant] %}
      {% if row.bound == "lower" %}{% assign relation = "\ge" %}{% else %}{% assign relation = "\le" %}{% endif %}
      <tr>
        <td><a href="{{ site.baseurl }}/constants/{{ row.constant }}">{{ constant.name }}</a></td>
        <td class="text-nowrap">
          {% if row.literature %}
            ${{ relation }} {{ row.literature.latex }}$
          {% else %}
            <span class="text-muted">none</span>
          {% endif %}
        </td>
        <td class="text-nowrap">
          {% if row.attested %}
            {% assign attested_cert = constant.certificates | where: "id", row.attested_certificate | first %}
            <a href="{{ attested_cert.attestation.checker }}">${{ relation }} {{ row.attested.latex }}$</a>
          {% else %}
            <span class="text-muted">none</span>
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
          {% if row.evidence == "witness" %}
            <span class="badge bg-success">Witness</span>
          {% else %}
            <span class="badge bg-secondary">Lean proof</span>
          {% endif %}
        </td>
        <td>
          {% assign source = site.data.sources[row.source] %}
          {% if source.doi %}
            <a href="{{ source.doi }}">{{ source.string }}</a>
          {% elsif source.url %}
            <a href="{{ source.url }}">{{ source.string }}</a>
          {% else %}
            {{ source.string }}
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
