---
layout: default
title: Download
permalink: /download/
---

# Download

The data on bounds and value updates is available for download in several formats. In some cases, the YAML and JSON files contain more information than the tabular files, such as a description and list of updates for each constant. These are included for convenience, but can also be derived by cross-referencing the information across tabular files.

<table class="table table-bordered">
  <thead>
    <tr>
      <th>Data</th>
      <th>YAML</th>
      <th>JSON</th>
      <th>CSV</th>
      <th>TSV</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td><strong>Constants</strong><br>All constants with their current bounds or value</td>
      <td><a href="{{ site.baseurl }}/data/constants.yml">constants.yml</a></td>
      <td><a href="{{ site.baseurl }}/data/constants.json">constants.json</a></td>
      <td><a href="{{ site.baseurl }}/data/constants.csv">constants.csv</a></td>
      <td><a href="{{ site.baseurl }}/data/constants.tsv">constants.tsv</a></td>
    </tr>
    <tr>
      <td><strong>Families</strong><br>Metadata about families of related constants</td>
      <td><a href="{{ site.baseurl }}/data/families.yml">families.yml</a></td>
      <td><a href="{{ site.baseurl }}/data/families.json">families.json</a></td>
      <td><a href="{{ site.baseurl }}/data/families.csv">families.csv</a></td>
      <td><a href="{{ site.baseurl }}/data/families.tsv">families.tsv</a></td>
    </tr>
    <tr>
      <td><strong>History</strong><br>Each bound that improved on the earlier ones, with its discovery (a source or a certificate) and its best evidence</td>
      <td><a href="{{ site.baseurl }}/data/history.yml">history.yml</a></td>
      <td><a href="{{ site.baseurl }}/data/history.json">history.json</a></td>
      <td><a href="{{ site.baseurl }}/data/history.csv">history.csv</a></td>
      <td><a href="{{ site.baseurl }}/data/history.tsv">history.tsv</a></td>
    </tr>
    <tr>
      <td><strong>Updates</strong><br>Bounds from the literature, each citing the source that first gave it</td>
      <td><a href="{{ site.baseurl }}/data/updates.yml">updates.yml</a></td>
      <td><a href="{{ site.baseurl }}/data/updates.json">updates.json</a></td>
      <td><a href="{{ site.baseurl }}/data/updates.csv">updates.csv</a></td>
      <td><a href="{{ site.baseurl }}/data/updates.tsv">updates.tsv</a></td>
    </tr>
    <tr>
      <td><strong>Sources</strong><br>Metadata for the sources cited for bounds from the literature</td>
      <td><a href="{{ site.baseurl }}/data/sources.yml">sources.yml</a></td>
      <td><a href="{{ site.baseurl }}/data/sources.json">sources.json</a></td>
      <td><a href="{{ site.baseurl }}/data/sources.csv">sources.csv</a></td>
      <td><a href="{{ site.baseurl }}/data/sources.tsv">sources.tsv</a></td>
    </tr>
    <tr>
      <td><strong>Certificates</strong><br>Checked evidence for bounds, who submitted it, and the role each plays in its constant's history (<a href="{{ site.baseurl }}/contributions/#recent-certificates">browse recent</a>)</td>
      <td><a href="{{ site.baseurl }}/data/certificates.yml">certificates.yml</a></td>
      <td><a href="{{ site.baseurl }}/data/certificates.json">certificates.json</a></td>
      <td><a href="{{ site.baseurl }}/data/certificates.csv">certificates.csv</a></td>
      <td><a href="{{ site.baseurl }}/data/certificates.tsv">certificates.tsv</a></td>
    </tr>
    <tr>
      <td><strong>Unverified bounds</strong><br>Current bounds whose best evidence isn't a verified certificate yet (<a href="{{ site.baseurl }}/unverified/">browse</a>)</td>
      <td><a href="{{ site.baseurl }}/data/unverified_bounds.yml">unverified_bounds.yml</a></td>
      <td><a href="{{ site.baseurl }}/data/unverified_bounds.json">unverified_bounds.json</a></td>
      <td><a href="{{ site.baseurl }}/data/unverified_bounds.csv">unverified_bounds.csv</a></td>
      <td><a href="{{ site.baseurl }}/data/unverified_bounds.tsv">unverified_bounds.tsv</a></td>
    </tr>
  </tbody>
</table>
