---
layout: default
title: About
permalink: /about/
---

# About

Leaps in Bounds was created and organized by [Daniel Munro](https://danmun.ro).

The source code is available on [GitHub](https://github.com/daniel-munro/leaps-in-bounds).

Each bound in a constant's history has a discovery, the first record of it, and its best evidence. Bounds from the literature are compiled from many sources, and the source where each first appeared is cited whenever possible, along with any survey or database it was collected in. Others were discovered by [certificates](#certificates) submitted here, which are also evidence for bounds from the literature when they're checked here. Many have been added by [contributors]({{ site.baseurl }}/contributions/#contributors).

<span class="badge text-bg-warning">Note</span> The histories of constants shown here are not necessarily complete. This applies to current best bounds or exact values, as well as updates prior to the current best ones. Further contributions to this repository will fill in missing updates.

## Certificates

A [certificate]({{ site.repository }}/blob/main/certificates/README.md) is evidence for a bound that a program can check: an explicit construction checked by a program, or a formal proof in Lean. A verified certificate has been checked here. Anyone can submit one, and each is credited to the GitHub account that submitted it.

A certificate can be the discovery of a bound or its best evidence. It's the discovery of a <span class="badge bg-verified-new">New bound</span> when no earlier source or certificate has a bound as strong. Otherwise it's evidence for a bound discovered earlier, usually in the literature, and stronger evidence than a paper's proof. See the [unverified bounds]({{ site.baseurl }}/unverified/) for current bounds that don't have a verified certificate yet.

Some certificates are <span class="badge bg-attested">Attested</span> instead: their evidence is too slow to check here so far, or too large to keep here, and someone else says they checked it with a checker they published. Anyone can run that checker on the evidence, but until it's checked here, an attested bound isn't verified.

See the [latest discoveries, contributors and recent certificates]({{ site.baseurl }}/contributions/), and download all certificates as [YAML]({{ site.baseurl }}/data/certificates.yml), [JSON]({{ site.baseurl }}/data/certificates.json), [CSV]({{ site.baseurl }}/data/certificates.csv) or [TSV]({{ site.baseurl }}/data/certificates.tsv).

## Related Projects

- [Big O Speedrun](https://bigospeedrun.com) - Leaderboards of recent progress on bounds for algorithm running times and other constants, with Lean-verified submissions.
- [Optimization Constants in Mathematics](https://github.com/teorth/optimizationproblems) - A curated collection of optimization constants in mathematics, often arising from solving a variational problem, or finding the best constant in a functional inequality.
