---
layout: default
permalink: /
---

<div class="hero text-center pt-3 pb-5">
  <img src="/assets/images/logo.png" alt="Leaps in Bounds Logo" class="img-fluid mb-4" style="max-width: 200px;">
  <h1 class="display-4 fw-bold">Leaps in Bounds</h1>
  <p class="lead mt-3">Repository of progress on mathematical unknowns</p>
</div>

This is a collaborative effort to compile data on historical progress on solved and unsolved mathematical constants. The focus is on quantitative updates, such as the lower and upper bounds on their values.

This site provides browsing, visualizations, and access to the structured data for other uses.

{% include constant_group_status.html %}

## Recently verified

{% assign batches = site.data.certificates | group_by_exp: "cert", "cert.date | append: ' ' | append: cert.submitted_by" %}
<ul>
  {% for batch in batches limit: 5 %}
    {% assign first = batch.items.first %}
    <li>
      {{ first.date }}, <a href="https://github.com/{{ first.submitted_by }}">{{ first.submitted_by }}</a>:
      {% if batch.size == 1 %}
        {% assign constant = site.data.constants[first.constant] %}
        {% if first.bound == "lower" %}{% assign relation = "\ge" %}{% else %}{% assign relation = "\le" %}{% endif %}
        <a href="{{ site.baseurl }}/constants/{{ first.constant }}">{{ constant.name }}</a> ${{ relation }} {{ first.value.latex }}$
        {% include certificate_comparison.html cert=first %}
      {% else %}
        {% assign group_ids = batch.items | map: "group" | uniq %}
        {{ batch.size }} certificates, in
        {% if group_ids.size > 4 %}{% assign shown = 3 %}{% else %}{% assign shown = 4 %}{% endif %}
        {% for group_id in group_ids limit: shown %}{{ site.data.constant_groups[group_id].name }}{% unless forloop.last %}; {% endunless %}{% endfor %}{% if group_ids.size > shown %}; and {{ group_ids.size | minus: shown }} more groups{% endif %}
      {% endif %}
    </li>
  {% endfor %}
</ul>

See [all verified bounds]({{ site.baseurl }}/verified/) and [contributors]({{ site.baseurl }}/contributors/).

## Contributing

Contributions are welcome, from people and AI agents alike. Pull requests are the preferred way to contribute:

- **Bounds from the literature:** add published bounds, their sources, and earlier steps in their history, or new constants and groups of constants. See [how to add them](https://github.com/daniel-munro/leaps-in-bounds/blob/main/source_data/README.md).
- **Verified bounds:** submit a certificate, either a construction checked by a program or a proof in Lean. See [how to submit one](https://github.com/daniel-munro/leaps-in-bounds/blob/main/certificates/README.md), and the [unverified bounds]({{ site.baseurl }}/unverified/) for bounds from the literature that don't have one yet.

For more open-ended contributions, such as asking whether a group of constants fits or sharing data you're not sure how to add, start a [GitHub Discussion](https://github.com/daniel-munro/leaps-in-bounds/discussions). For technical problems and suggestions, [open an issue](https://github.com/daniel-munro/leaps-in-bounds/issues).

Contributions are credited to the GitHub account that made them on the [contributors page]({{ site.baseurl }}/contributors/).

To have an AI agent contribute, give it one of these prompts:

<pre class="border rounded p-3" style="white-space: pre-wrap;"><code>Read https://github.com/daniel-munro/leaps-in-bounds/blob/main/certificates/README.md and follow it to submit a verified bound to Leaps in Bounds.</code></pre>

<pre class="border rounded p-3" style="white-space: pre-wrap;"><code>Read https://github.com/daniel-munro/leaps-in-bounds/blob/main/source_data/README.md and follow it to add missing bounds from the literature to Leaps in Bounds, for &lt;group or topic&gt;.</code></pre>

## Related Projects

- [Big O Speedrun](https://bigospeedrun.com) - Leaderboards of recent progress on bounds for algorithm running times and other constants, with Lean-verified submissions.
- [Optimization Constants in Mathematics](https://github.com/teorth/optimizationproblems) - A curated collection of optimization constants in mathematics, often arising from solving a variational problem, or finding the best constant in a functional inequality.
