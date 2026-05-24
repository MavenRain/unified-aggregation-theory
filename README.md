# unified-aggregation-theory

A Lean 4 formalization of the **unification of three classical aggregation
theorems** as regimes of a single categorical construction:

- **Arrow-Debreu Equilibrium** (decentralized market aggregation under
  convexity)
- **Arrow's Impossibility Theorem** (Chichilnisky's topological
  formulation; obstruction to democratic preference aggregation)
- **Schelling segregation as Ising with ferromagnetic Hamiltonian**
  (emergent community structure via spontaneous symmetry breaking)

The unifying mechanism is the **left Kan extension of a choice rule
along the orbit projection** into the action groupoid of a symmetry
group acting on the configuration category.  The Brock-Durlauf
statistical-mechanics-of-discrete-choice β-family is the parametrized
linker that passes through all three regimes via two phase transitions.

Built on [`comp-cat-theory`](../comp-cat-theory) for the categorical
primitives (Category, Functor, NatTrans, LeftKanExtension) and
[`arrow-cat`](../arrow-cat) for the Arrow-Impossibility regime
(Geanakoplos pivotal-voter argument, complete with zero `sorry`s).

> No Mathlib dependency.  All categorical, social-choice, and
> statistical-mechanics primitives are drawn from the comp-cat-theory
> reservoir and the arrow-cat extension, with anything else built from
> scratch.

## Status

**Phase 0**: scaffold complete; type-level definitions only.  Theorems
compile under `sorry`.  Subsequent phases fill in proofs.

## Phases

- **Phase 0** (current): repo scaffold plus type-level statement of the
  framework: `ConfigSpace`, `ChoiceRule`, `Aggregation`, `Regimes`,
  `Trichotomy`.  No proofs.
- **Phase 1a**: wire `arrow-cat` into the Arrow-Impossibility regime.
  Bridging definition (equivariance on `Lan_p F` corresponds to
  arrow-cat's anonymity hypothesis) plus the connecting theorem.
- **Phase 1b**: prove Schelling-Ising mean-field with Z_2 symmetry
  end-to-end.  Universal cocone of `Lan_p F_β` has one connected
  component for β < β_c and two for β > β_c.
- **Phase 2**: Arrow-Debreu regime via Kakutani fixed-point.

## Architecture

```
UnifiedAggregation/
  ConfigSpace.lean    SymmetryGroup, GAction on a category
  ChoiceRule.lean     Functor C ⥤ D, β-parameterized family
  Aggregation.lean    OrbitGroupoid, orbitProjection, Aggregation
                      (= LeftKanExtension along the orbit projection)
  Regimes.lean        IsArrowDebreuRegime, IsArrowImpossibilityRegime,
                      IsSchellingIsingRegime
  Trichotomy.lean     The unification theorem statement
```

Every tactic block (when present) uses only kan-tactics.  No `panic!`,
`throw`, or `unreachable!` anywhere; `Option` and `Except` are used
wherever a partial function or failable operation appears.

## Building

```sh
lake update
lake build
```

The repository is a reservoir library: downstream projects can depend
on it via:

```toml
[[require]]
name = "unified-aggregation-theory"
path = "../unified-aggregation-theory"
```

or as a git dependency once published.

## Documentation

API documentation is auto-generated via
[`doc-gen4`](https://github.com/leanprover/doc-gen4) and published to
GitHub Pages on every push to `main` (workflow at
`.github/workflows/docs.yml`).  Once the repository is hosted on
GitHub, docs will be available at
`https://MavenRain.github.io/unified-aggregation-theory/`.

Local doc build:

```sh
lake build UnifiedAggregation:docs
# Output: .lake/build/doc/index.html
```

Note: local doc builds require a configured git remote so that
`doc-gen4` can generate source-line links.  On a freshly-init'd repo
without a remote, the doc build will fail at the final source-URI
step; this is expected and will succeed in CI once the repo is
pushed to GitHub.

## License

Dual-licensed under MIT OR Apache-2.0, at your option.
