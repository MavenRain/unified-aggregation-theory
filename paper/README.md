# Companion paper: Lean 4 formalization of the aggregation-theory unification

This directory contains the LaTeX source for the companion preprint to
the `unified-aggregation-theory` Lean 4 formalization.

## Status

**Draft, in progress.**  Sections currently filled in:

- Abstract
- Introduction (`\section{Introduction}`)
- The Central Object and the Three Regimes (`\section{The Central Object...}`)
- Phase 1a: Arrow-Impossibility (`\section{Phase 1a...}`), with the
  full proof sketch of `no_equivariant_constrained_swf`

Sections stubbed for expansion:

- Foundations (discrete categories, GAction, OrbitGroupoid, Functor
  extensionality)
- Phase 1b: Schelling-Ising symbolic bifurcation
- Discussion (related work, open regimes, sorries)

## Building

```sh
pdflatex main.tex
pdflatex main.tex
# or:
latexmk -pdf main.tex
```

## Target venue

arXiv (cs.LO or math.CT primary).  Length target: 10-15 pages.

## License

Same as the parent repository: dual MIT/Apache-2.0.
