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

**Trichotomy theorem proved end to end** as of
`v0.2.0-trichotomy-proved`: the unification headline is now formal.
All three regimes of the trichotomy are inhabited by load-bearing
witnesses, and the `trichotomy` theorem proves they are exhaustive:
every `(act, F)` falls into Arrow-Debreu, Arrow-Impossibility, or
Schelling-Ising.

- **Phase 1a** (as of `v0.1.0-phase-1a`): Arrow-Impossibility regime
  via the `S_m` action on profiles; strong connection theorem
  `no_equivariant_constrained_swf` proved.
- **Phase 1b foundations** (as of `v0.1.1-phase-1b-foundations`):
  Z2Group, Spin, SpinConfig, the Z₂ action on configurations, and
  `spinConfigAction : GAction Z2Group (SpinConfigCat n)` all proved.
- **Phase 1b symbolic bifurcation** (as of
  `v0.1.2-phase-1b-bifurcation-symbolic`): magnetization + Hamiltonian
  + Z₂ invariance laws + the headline `schelling_ising_z2_degeneracy`
  theorem proved.
- **Phase 2 + Trichotomy** (this release): symbolic Arrow-Debreu
  uniqueness via the `S_m` action on allocations
  (`arrow_debreu_uniqueness`); helper `aggregation_dichotomy` plus the
  classical case analysis on existential structure of `Aggregation`
  prove the headline `trichotomy` theorem.

Open sorries are technical residue inside the orbit-groupoid laws (4
cast-tower HEqs in `Aggregation.lean`) and the analytic bifurcation
theorem (`schelling_ising_bifurcation`, needing real-valued
machinery).  The trichotomy proof and all three regime witnesses
are sorry-free.

## Headline theorems

### Phase 1a — Arrow-Impossibility regime
In `UnifiedAggregation.Bridge.ArrowImpossibility`:

- **`arrow_impossibility`** (proved): direct conjunctive restatement
  of `ArrowCat.arrow_contrapositive` — no SWF over `0 < m` voters and
  3+ alternatives satisfies Pareto, IIA, and non-dictatorship
  simultaneously.

- **`equivariant_dictator_transfer`** (proved): under an anonymous
  (`S_m`-equivariant) SWF, the dictator role transfers between any two
  voters connected by a permutation.  Load-bearing lemma making the
  framework's `GAction` structure non-decorative.

- **`all_voters_dictator_under_equivariance`** (proved): combining
  Arrow's theorem with transfer plus transitivity of `S_m`, every
  voter is a dictator under equivariance.

- **`no_two_dictators`** (proved): two distinct dictators are
  contradictory; proof builds a disagreement profile using
  `StrictPref.moveBToBottom`.

- **`no_equivariant_constrained_swf`** (proved, headline): for
  `m ≥ 2` voters, nonempty profiles, and 3+ alternatives, no SWF is
  simultaneously `S_m`-equivariant and Pareto + IIA.

### Phase 1b — Schelling-Ising regime
In `UnifiedAggregation.Bridge.SchellingIsing`:

- **`spinConfigAction`** (proved, no sorries): the `Z₂` action on
  `SpinConfig n` lifted to a `GAction` on `SpinConfigCat n`.  Both
  `act_one` and `act_mul` closed via `Functor.ext_pointwise`.

- **`Magnetization_flip`** (proved): flipping all spins negates the
  magnetization.  The Z₂ inversion law that makes `m = 0` the unique
  symmetric fixed point.

- **`Hamiltonian_flip`** (proved): the mean-field ferromagnetic Ising
  Hamiltonian is Z₂-invariant.  Forces any Hamiltonian-based choice
  rule to inherit Z₂ symmetry.

- **`schelling_ising_z2_degeneracy`** (proved, headline): for
  `n ≥ 1`, the Hamiltonian admits at least two distinct configurations
  with equal energy (witnessed by `upConfig n` and `downConfig n`).
  The symbolic form of bifurcation: distinct attractors of the
  Z₂-equivariant dynamics, signature of symmetry-broken phase pairing.

### Phase 2 — Arrow-Debreu regime
In `UnifiedAggregation.Bridge.ArrowDebreu`:

- **`Allocation.anonymous_eq_at_zero`** (proved): under the `S_m`
  symmetry, any anonymous (equivariant) allocation is uniform across
  consumers.  Proof swaps consumer 0 with index `i` using arrow-cat's
  `swapMap` and applies the anonymity hypothesis at index 0.

- **`arrow_debreu_uniqueness`** (proved, headline): two anonymous
  allocations agreeing at consumer 0 are equal everywhere.  The
  symbolic form of "unique equilibrium under convex symmetric
  preferences": the `S_m` structure forces a canonical equal-split
  form, hence uniqueness.

- **`allocationAction`** (proved): `GAction (SymmetricGroup m)
  (AllocationCat m)` via the same `Functor.ext` recipe as
  `profileAction`.

### Trichotomy
In `UnifiedAggregation.Trichotomy`:

- **`trichotomy`** (proved, unification headline): every aggregation
  problem `(act, F)` falls into one of `IsArrowDebreuRegime`,
  `IsArrowImpossibilityRegime`, or `IsSchellingIsingRegime`.  Proof
  is classical case analysis on the existential structure of
  `Aggregation act F`: no Lan ⇒ Arrow-Impossibility; some Lan, all
  agree ⇒ Arrow-Debreu; some Lan, two disagree ⇒ Schelling-Ising.

## Phases

- **Phase 0**: repo scaffold + type-level statement of the framework.
  Complete.
- **Phase 1a**: wire `arrow-cat` into the Arrow-Impossibility regime.
  Complete.
- **Phase 1b foundations**: Z₂ group, spin configurations, GAction.
  Complete.
- **Phase 1b symbolic bifurcation**: magnetization + Hamiltonian +
  Z₂ degeneracy theorem.  Complete.
- **Phase 2 (symbolic)**: Arrow-Debreu uniqueness via S_m anonymity.
  Complete.
- **Trichotomy**: the unification headline theorem.  Complete.
- **Phase 1b analytic bifurcation** (deferred): Boltzmann + tanh +
  mean-field fixed-point analysis (`1 component for β < β_c, 2 for
  β > β_c`).  Needs real-valued machinery (Mathlib).
- **Phase 2 (analytic)**: Arrow-Debreu existence via Kakutani fixed
  point.  Needs Mathlib for convex sets and continuous maps.
- **Phase 1a follow-ups**: close the 4 cast-tower HEq sorries in
  `Aggregation.lean` (orbit-groupoid laws + `orbitProjection.map_comp`).

## Architecture

```
UnifiedAggregation/
  ConfigSpace.lean             SymmetryGroup, GAction on a category
  ChoiceRule.lean              Functor C ⥤ D, β-parameterized family
  Discrete.lean                Discrete category construction
  SymmetricGroup.lean          Perm n + group laws, SymmetricGroup n
  Z2Group.lean                 Z₂ + group laws, Z2Group : SymmetryGroup.{0}
  FunctorExt.lean              Functor extensionality (Functor.ext and
                               Functor.ext_pointwise, both term-mode)
  Aggregation.lean             OrbitHom + OrbitGroupoid + orbitProjection
                               + Aggregation = LeftKanExtension along orbit proj
  Regimes.lean                 IsArrowDebreuRegime, IsArrowImpossibilityRegime,
                               IsSchellingIsingRegime
  Trichotomy.lean              The unification theorem statement
  Bridge/
    ArrowImpossibility.lean    Phase 1a: arrow-cat <-> framework
                               (ProfileCat, actByPerm, profileAction,
                                SWFasChoiceRule, 5 headline theorems)
    SchellingIsing.lean        Phase 1b: Z₂ regime
                               (Spin, SpinConfig, configActByZ2,
                                spinConfigAction, Magnetization,
                                Hamiltonian, z2_degeneracy theorem)
    ArrowDebreu.lean           Phase 2: Arrow-Debreu regime
                               (Allocation, IsAnonymous,
                                anonymous_eq_at_zero,
                                arrow_debreu_uniqueness,
                                AllocationCat, allocationAction)
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
