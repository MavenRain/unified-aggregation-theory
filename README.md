# unified-aggregation-theory

A Lean 4 formalization exhibiting three classical aggregation phenomena
as the three regimes of a **single** categorical construction: the
**left Kan extension of a choice rule along the orbit projection** into
the action groupoid of a symmetry group acting on a configuration
category,

```
Aggregation act F := LeftKanExtension (orbitProjection act) F.
```

The regime a problem occupies is determined by the existence and
object-uniqueness of this Kan extension:

- **Arrow-Impossibility** — *no* aggregation exists.  A Pareto + IIA
  social welfare function (Arrow's theorem in Geanakoplos pivotal-voter
  form, via [`arrow-cat`](../arrow-cat)) is forced to be non-anonymous,
  and a choice rule that is not constant on orbits admits no left Kan
  extension.
- **Arrow-Debreu** — a *unique* aggregation exists.  Realized by the
  mean-field choice rule below the critical temperature (`β ≤ 1`): a
  single phase (`m = 0`), so the aggregate order parameter is uniquely
  determined.
- **Schelling-Ising** — an aggregation exists but is *not* object-unique.
  Realized by the same choice rule above the critical temperature
  (`β > 1`): the spontaneously symmetry-broken pair `±m_*`, so the
  universal aggregate is pinned only up to the residual `Z₂` symmetry.

The mean-field Brock-Durlauf β-family is the parametrized linker between
the Arrow-Debreu and Schelling-Ising regimes: the cardinality of the
mean-field fixed-point set (computed by `mean_field_bifurcation`) is the
number of phases, which bifurcates from one to two at `β_c = 1`.

## Scope, stated honestly

This formalization makes a precise and limited claim, and it is worth
being explicit about what is and is not proved:

- The **construction is genuinely single**: all three regime witnesses
  instantiate the *same* `Aggregation` definition, differing only in the
  configuration category, the symmetry action, and the choice rule.
- The **"Arrow-Debreu regime" is object-uniqueness of the aggregation
  under symmetry**, not the Arrow-Debreu / Kakutani general-equilibrium
  existence theorem (which is *not* formalized here).
- The **Schelling-Ising regime is non-uniqueness at the level of object
  equality.**  Into a *discrete* outcome category it cannot occur at all
  (`Characterization.not_schelling_ising_discrete`: any two left Kan
  extensions into a discrete category agree on objects).  This is exactly
  why the order-parameter target is the *indiscrete phase groupoid* on
  the mean-field fixed-point set: there distinct objects are isomorphic
  yet unequal, so the symmetry-broken phases are genuinely distinct
  realizations of the universal object.
- The **`trichotomy` theorem itself is a classical case split** on
  existence and object-uniqueness, hence exhaustive for any predicate.
  Its content comes from the *inhabitation* theorem
  `trichotomy_regimes_realized`, which shows each regime is occupied by a
  real aggregation phenomenon, not from the case split alone.

Built on [`comp-cat-theory`](../comp-cat-theory) for the categorical
primitives (Category, Functor, NatTrans, LeftKanExtension),
[`kan-tactics`](../kan-tactics) for the proof tactics (every `by` block
uses only kan-tactics), and [`arrow-cat`](../arrow-cat) for the
Arrow-Impossibility regime (Geanakoplos pivotal-voter argument, zero
`sorry`s).

> Mathlib is pulled for the analytic content (real numbers, `Real.tanh`,
> the real-analysis machinery behind the mean-field bifurcation).  All
> categorical, social-choice, and Int-level statistical-mechanics
> primitives come from the comp-cat-theory reservoir and arrow-cat.

## Status

**Genuine trichotomy: exhaustive *and* inhabited.**  The `trichotomy`
theorem proves the three regimes are jointly exhaustive (every `(act, F)`
lands in some regime), and `trichotomy_regimes_realized` proves all three
are genuinely inhabited — each by an actual aggregation phenomenon
realized through the single `Aggregation` construction:

- Arrow-Impossibility: `Bridge.ArrowImpossibility.arrow_impossibility_regime`
  (Pareto + IIA ⟹ no aggregation, via Arrow's theorem and
  `Characterization.lan_implies_orbit_constant`).
- Arrow-Debreu: `Bridge.SchellingIsing.paramagnetic_arrow_debreu_regime`
  (`β ≤ 1`, unique phase ⟹ object-unique aggregation).
- Schelling-Ising: `Bridge.SchellingIsing.schelling_ising_regime`
  (`β > 1`, symmetry-broken pair ⟹ object-non-unique aggregation).

The discrete-target obstruction
`Characterization.not_schelling_ising_discrete` is the *proved* reason
the Schelling-Ising regime requires the indiscrete phase target.  The
earlier discrete "shadow" results (`arrow_debreu_uniqueness`,
`schelling_ising_z2_degeneracy`) are supporting lemmas about the
configuration categories, not the regime witnesses.

**The entire framework is sorry-free.**  Both sides of the mean-field
bifurcation theorem are formally proved:

- `unique_fixed_point_paramagnetic` (β ≤ 1 ⟹ m = 0 unique) follows
  from `Real.tanh_strictMono` (via the `sinh y · cosh x - sinh x ·
  cosh y = sinh(y − x)` identity) and `Real.tanh_lt_self_of_pos`
  (via `strictMonoOn_of_hasDerivWithinAt_pos` on
  `g(t) = t·cosh t − sinh t`).
- `bifurcation_ferromagnetic` (β > 1 ⟹ symmetry-broken pair exists)
  follows from `Real.hasDerivAt_tanh`, `Real.tanh_gt_self_sub_sq`, and
  `intermediate_value_Icc'` applied to `f(m) = tanh(β·m) − m` on
  `[δ, 1]` with `δ := (β−1)/β²`; the symmetric fixed point follows from
  `Real.tanh_neg`.

All four orbit-groupoid cast-tower HEqs in `Aggregation.lean`
(`orbitProjection.map_comp`, `comp_id`, `id_comp`, `assoc`) are closed
through the in-house tactic stack in `UnifiedAggregation.HeqTransport`.

## Headline theorems

### The single construction
In `UnifiedAggregation.Aggregation`:

- **`Aggregation act F := LeftKanExtension (orbitProjection act) F`** —
  the one construction every regime instantiates.

### Characterization (what makes the regimes meaningful)
In `UnifiedAggregation.Characterization`:

- **`not_schelling_ising_discrete`** (proved): into a discrete target the
  Schelling-Ising regime is empty (left Kan extensions are object-unique
  there).  This is the obstruction that forces the phase-groupoid target.
- **`lan_implies_orbit_constant`** (proved): existence of an aggregation
  over a discrete target forces the choice rule to be constant on orbits
  (anonymity).  The bridge turning Arrow's theorem into impossibility-
  regime membership.

### Genuine regime realization
In `UnifiedAggregation.TrichotomyWitnesses`:

- **`trichotomy_regimes_realized`** (proved, headline): all three regimes
  are inhabited by the single `Aggregation` construction.
- **`dictator_pareto_iia`** (proved): a dictator is a Pareto + IIA SWF,
  so the Arrow-Impossibility regime is non-vacuously occupied.

In `UnifiedAggregation.Bridge.ArrowImpossibility`:

- **`arrow_impossibility_regime`** (proved): for `m ≥ 2` voters and 3+
  alternatives, every Pareto + IIA social welfare function occupies the
  Arrow-Impossibility regime (its orbit-projection left Kan extension
  does not exist).

In `UnifiedAggregation.Bridge.SchellingIsing`:

- **`paramagnetic_arrow_debreu_regime`** (proved): for `β ≤ 1` the
  mean-field choice rule occupies the Arrow-Debreu regime (object-unique
  aggregation).
- **`schelling_ising_regime`** (proved): for `β > 1` the same rule
  occupies the Schelling-Ising regime (object-non-unique aggregation, the
  symmetry-broken pair).

### Supporting results
- **`no_equivariant_constrained_swf`** (`Bridge.ArrowImpossibility`):
  for `m ≥ 2`, no SWF is simultaneously `S_m`-equivariant and Pareto +
  IIA.  The social-choice engine behind `arrow_impossibility_regime`.
- **`mean_field_bifurcation`** (`Bridge.SchellingIsing`): the
  self-consistency equation `m = tanh(β·m)` has the unique solution
  `m = 0` for `β ≤ 1` and a symmetry-broken pair for `β > 1`.  The
  analytic engine behind the Arrow-Debreu and Schelling-Ising witnesses.
- **`arrow_debreu_uniqueness`** (`Bridge.ArrowDebreu`),
  **`schelling_ising_z2_degeneracy`** (`Bridge.SchellingIsing`): discrete
  configuration-category facts (anonymous-allocation uniformity, Z₂
  ground-state degeneracy) that motivate the regimes.

### Trichotomy (exhaustiveness)
In `UnifiedAggregation.Trichotomy`:

- **`trichotomy`** (proved): every aggregation problem `(act, F)` falls
  into `IsArrowDebreuRegime`, `IsArrowImpossibilityRegime`, or
  `IsSchellingIsingRegime`.  Classical case analysis on the existential
  structure of `Aggregation act F`.

## Architecture

```
UnifiedAggregation/
  ConfigSpace.lean             SymmetryGroup, GAction on a category
  ChoiceRule.lean              Functor C ⥤ D, β-parameterized family
  Discrete.lean                Discrete category construction
  Indiscrete.lean              Indiscrete (phase) groupoid: one morphism
                               between any two objects; constIndiscrete;
                               indiscreteLan (Lan into an indiscrete target)
  SymmetricGroup.lean          Perm n + group laws, SymmetricGroup n
  Z2Group.lean                 Z₂ + group laws, Z2Group : SymmetryGroup.{0}
  FunctorExt.lean              Functor extensionality (term-mode)
  HeqTransport.lean            HEq cast-stripping tactics for the
                               orbit-groupoid category laws
  Aggregation.lean             OrbitHom + OrbitGroupoid + orbitProjection
                               + Aggregation = LeftKanExtension along orbit proj
  Regimes.lean                 IsArrowDebreuRegime, IsArrowImpossibilityRegime,
                               IsSchellingIsingRegime
  Characterization.lean        lan_obj_unique_discrete /
                               not_schelling_ising_discrete (the
                               discrete-target obstruction) and
                               lan_implies_orbit_constant (anonymity bridge)
  Trichotomy.lean              The exhaustiveness theorem
  TrichotomyWitnesses.lean     trichotomy_regimes_realized: all three
                               regimes inhabited by the one construction
  Bridge/
    ArrowImpossibility.lean    Arrow-cat <-> framework; profileAction,
                               SWFasChoiceRule, no_equivariant_constrained_swf,
                               arrow_impossibility_regime
    SchellingIsing.lean        Z₂ regime; spinConfigAction, Magnetization,
                               Hamiltonian, mean_field_bifurcation, MagPhase,
                               paramagnetic_arrow_debreu_regime,
                               schelling_ising_regime
    ArrowDebreu.lean           Allocation, IsAnonymous, arrow_debreu_uniqueness,
                               allocationAction (configuration-category facts)
```

Every tactic block uses **only** kan-tactics; steps with no
Kan-extension surface (classical case analysis, destructuring, structure-
field substitution) are written in **term mode**, which the convention
permits.  The single principled boundary is the **mean-field bifurcation
theorem** (the `Real.tanh` development in `Bridge.SchellingIsing`),
proved against Mathlib's real-analysis library and its arithmetic
decision procedures — a declared dependency boundary, not a gap in
kan-tactics' categorical span.

No `panic!`, `throw`, or `unreachable!` anywhere; `Option` and `Except`
are used wherever a partial function or failable operation appears.

## Building

```sh
lake update
lake build
```

The repository is a reservoir library: downstream projects can depend on
it via:

```toml
[[require]]
name = "unified-aggregation-theory"
git = "https://github.com/MavenRain/unified-aggregation-theory.git"
rev = "main"
```

## Documentation

API documentation is auto-generated via
[`doc-gen4`](https://github.com/leanprover/doc-gen4).  Local doc build:

```sh
lake build UnifiedAggregation:docs
# Output: .lake/build/doc/index.html
```

## License

Dual-licensed under MIT OR Apache-2.0, at your option.
