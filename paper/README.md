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
information are now filled in. Before submission, add a repository DOI and release version if
available; the proof and validation records remain in `proof_work/publication_validation/`.

Current artifact hashes (also recorded in the review-bundle manifest):

```text
842ddd54353d1d0e76035d774abdd347bf5dbb3f15f81dc4b34d318c470af5d2  main.tex
478e5b01fef0de3775190e03542054934ea0962a3eabe74bacb6b39017fe5d30  main.pdf
```

The compact submission source package `THOMSON_N9_MANUSCRIPT_SOURCE.zip` contains
those two files and has SHA-256
`4764b75a24cae9f6b9824507197610ddae321ed865d183438a368a2b96189ac4`.

For the operational upload sequence, see `SUBMISSION_GUIDE_zh.md`; the journal
letter template is `COVER_LETTER_TEMPLATE.md`.
