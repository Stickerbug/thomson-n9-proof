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

Current artifact hashes (also recorded in the review-bundle manifest):

```text
b16ed0528aed3c501795e304fb445897b6d340e844664d6e879d614242fcb499  main.tex\na0d7bef3a4f9638e0042801b00340a105d485fdb029f946b65e6130b0ca470c3  main.pdf
```

The compact submission source package `THOMSON_N9_MANUSCRIPT_SOURCE.zip` contains the manuscript source and PDF and has SHA-256\n`25e333a6cee8e879e441c2bd0c8430e8b2f1648e3008489a27eea864aea4815e`.

For the operational upload sequence, see `SUBMISSION_GUIDE_zh.md`; the journal
letter template is `COVER_LETTER_TEMPLATE.md`.
