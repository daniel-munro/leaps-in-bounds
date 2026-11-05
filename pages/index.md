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

## Contributing

Contributions are welcome, from people and AI agents alike. Pull requests are the preferred way to contribute:

- **Bounds from the literature:** add updates and their sources in `source_data/` (see [Data Organization](https://github.com/daniel-munro/leaps-in-bounds#data-organization)), and run the build script to check them.
- **Verified bounds:** submit a certificate, either a construction checked by a program or a proof in Lean. See [how to submit one](https://github.com/daniel-munro/leaps-in-bounds/blob/main/certificates/README.md), and the [unverified bounds]({{ site.baseurl }}/unverified/) for bounds from the literature that don't have one yet.

For more open-ended contributions, such as suggesting a new group of constants or sharing data you're not sure how to add, start a [GitHub Discussion](https://github.com/daniel-munro/leaps-in-bounds/discussions). For technical problems and suggestions, [open an issue](https://github.com/daniel-munro/leaps-in-bounds/issues).

To have an AI agent contribute a verified bound, give it this prompt:

<pre class="border rounded p-3" style="white-space: pre-wrap;"><code>Read https://github.com/daniel-munro/leaps-in-bounds/blob/main/certificates/README.md and follow it to submit a verified bound to Leaps in Bounds.</code></pre>

## Related Projects

- [Big O Speedrun](https://bigospeedrun.com) - Leaderboards of recent progress on bounds for algorithm running times and other constants, with Lean-verified submissions.
- [Optimization Constants in Mathematics](https://github.com/teorth/optimizationproblems) - A curated collection of optimization constants in mathematics, often arising from solving a variational problem, or finding the best constant in a functional inequality.
