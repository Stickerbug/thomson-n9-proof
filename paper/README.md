# Publication paper

`main.tex` is the current English manuscript for the frozen nine-point theorem. It is deliberately explicit about the validation boundary:

- the Lean theorem is compiler- and fresh-kernel-checked;
- the pure-Python tree checker is independent but conditional on the stated model/local premises;
- no congruence-uniqueness theorem is claimed;
- a second proof kernel and peer review remain future validation steps.

Compile with:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Author, affiliation, ORCID, corresponding-author email, funding, and conflict-of-interest
information are filled in. The archived release is GitHub tag `n9-proof-2026-10-23` with DOI
[10.5281/zenodo.23573472](https://doi.org/10.5281/zenodo.23573472). The proof and validation records remain in `proof_work/publication_validation/`.

Related work: Aravind Karthigeyan released an earlier public Lean/Nanoda formalization of the nine-point Coulomb Thomson problem (commit `168ff0c`, 6 October 2026; DOI [10.5281/zenodo.23192843](https://doi.org/10.5281/zenodo.23192843)). That project reports a stronger uniqueness statement. This repository makes no priority claim and should be compared as a separate certificate and validation implementation.

Current artifact hashes (also recorded in the review-bundle manifest):

```text
41e3cf0f8292e7ac3128ee0931a567090841172d5fb9606215c340c5a781bb93  main.tex
a21e60c139b3bc0cac7460c70516adf7975e38c4d84536c3c744cc8c14ac8633  main.pdf
```

The compact submission source package `THOMSON_N9_MANUSCRIPT_SOURCE.zip` contains the manuscript source and PDF and has SHA-256\n`25e333a6cee8e879e441c2bd0c8430e8b2f1648e3008489a27eea864aea4815e`.

The journal letter template is `COVER_LETTER_TEMPLATE.md`; the release and DOI
links above identify the current publication archive.
