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

**Phase 1a complete** as of `v0.1.0-phase-1a`: the categorical
embedding of Arrow's Impossibility Theorem into the unified framework
is fully built and the strong connection theorem is proved.

Open sorries are technical residue inside the orbit-groupoid laws (4
cast-tower HEqs in `Aggregation.lean`) and the unification trichotomy
statement (1 sorry in `Trichotomy.lean`, the long-term Phase 2+
target).

## Headline theorems

In `UnifiedAggregation.Bridge.ArrowImpossibility`:

- **`arrow_impossibility`** (proved): direct conjunctive restatement
  of `ArrowCat.arrow_contrapositive` — no SWF over `0 < m` voters and
  3+ alternatives satisfies Pareto, IIA, and non-dictatorship
  simultaneously.

- **`equivariant_dictator_transfer`** (proved): under an anonymous
  (`S_m`-equivariant) SWF, the dictator role transfers between any two
  voters connected by a permutation.  This is the load-bearing lemma
  that makes the framework's `GAction` structure non-decorative.

- **`all_voters_dictator_under_equivariance`** (proved): combining
  Arrow's theorem with transfer plus transitivity of `S_m` on `Fin m`,
  every voter is a dictator under equivariance.

- **`no_two_dictators`** (proved): two distinct dictators are
  contradictory.  Proof builds a disagreement profile using
  `StrictPref.moveBToBottom` from arrow-cat and applies the dictator
  hypothesis on both voters, hitting `StrictPref.asym` for the
  contradiction.

- **`no_equivariant_constrained_swf`** (proved, headline): for
  `m ≥ 2` voters, a nonempty profile space, and 3+ alternatives, no
  SWF is simultaneously `S_m`-equivariant and Pareto + IIA.
  arrow-cat's classical statement allows a dictator, but the
  framework's anonymity requirement rules that out.

## Phases

- **Phase 0**: repo scaffold + type-level statement of the framework
  (`ConfigSpace`, `ChoiceRule`, `Aggregation`, `Regimes`,
  `Trichotomy`).  Complete.
- **Phase 1a**: wire `arrow-cat` into the Arrow-Impossibility regime
  via the `S_m` action on profiles; prove the strong connection
  theorem.  Complete.
- **Phase 1b** (next): prove Schelling-Ising mean-field with `Z_2`
  symmetry end-to-end.  Universal cocone of `Lan_p F_β` has one
  connected component for `β < β_c` and two for `β > β_c`.
- **Phase 2**: Arrow-Debreu regime via Kakutani fixed-point.
- **Phase 1a follow-ups**: close the 4 cast-tower HEq sorries in
  `Aggregation.lean` (orbit-groupoid laws + `orbitProjection.map_comp`).

## Architecture

```
UnifiedAggregation/
  ConfigSpace.lean             SymmetryGroup, GAction on a category
  ChoiceRule.lean              Functor C ⥤ D, β-parameterized family
  Discrete.lean                Discrete category construction
  SymmetricGroup.lean          Perm n + group laws, SymmetricGroup n
  FunctorExt.lean              Functor extensionality (term-mode)
  Aggregation.lean             OrbitHom + OrbitGroupoid + orbitProjection
                               + Aggregation = LeftKanExtension along orbit proj
  Regimes.lean                 IsArrowDebreuRegime, IsArrowImpossibilityRegime,
                               IsSchellingIsingRegime
  Trichotomy.lean              The unification theorem statement
  Bridge/
    ArrowImpossibility.lean    Phase 1a: arrow-cat <-> framework
                               (ProfileCat, actByPerm, profileAction,
                                SWFasChoiceRule, the 5 headline theorems)
```

Every tactic block uses kan-tactics where feasible, with documented
exceptions where standard tactics (`apply`, `cases`, `simp`, `rw`,
`intro`, `let`) are required for HEq manipulation or rewrite chains
that kan-tactics does not yet cover.  No `panic!`, `throw`, or
`unreachable!` anywhere; `Option` and `Except` are used wherever a
partial function or failable operation appears.

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
