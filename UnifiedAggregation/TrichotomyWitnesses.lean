/-
  UnifiedAggregation.TrichotomyWitnesses

  The capstone: each of the three regimes of the trichotomy is genuinely
  occupied by a classical aggregation phenomenon, and every occupant is
  an instance of the *single* construction

      Aggregation act F := LeftKanExtension (orbitProjection act) F.

  - Arrow-Impossibility: a Pareto + IIA social welfare function has no
    aggregation (the orbit-projection left Kan extension does not exist),
    because Arrow's theorem forces it to be non-anonymous.
  - Arrow-Debreu: below the critical temperature the mean-field choice
    rule has a unique aggregation (one phase, `m = 0`).
  - Schelling-Ising: above the critical temperature the *same* choice
    rule has a non-unique aggregation (the symmetry-broken pair `±m_*`).

  `UnifiedAggregation.Trichotomy.trichotomy` shows every aggregation
  problem lands in at least one regime; the witnesses here show all three
  regimes are inhabited.  Together they upgrade the trichotomy from a
  taxonomy into a content-bearing classification realized by one functor
  -- which is precisely the claim of the project.

  The discrete-target obstruction
  `Characterization.not_schelling_ising_discrete` explains why the
  Schelling-Ising witness must use the indiscrete phase target rather
  than the discrete encoding the other two regimes use.
-/

import UnifiedAggregation.Trichotomy
import UnifiedAggregation.Characterization
import UnifiedAggregation.Bridge.ArrowImpossibility
import UnifiedAggregation.Bridge.SchellingIsing

set_option autoImplicit false

universe u

namespace UnifiedAggregation

open CompCatTheory ArrowCat UnifiedAggregation.Bridge

/-- A dictator (voter `0`) is a Pareto + IIA social welfare function.
This makes the Arrow-Impossibility regime *non-vacuously* occupied:
such functions exist, and `arrow_impossibility_regime` places every one
of them in the Arrow-Impossibility regime. -/
theorem dictator_pareto_iia {m : Nat} {α : Type u} (h1 : 0 < m) :
    SWF.Pareto (m := m) (α := α) (fun p => p ⟨0, h1⟩) ∧
    SWF.IIA (m := m) (α := α) (fun p => p ⟨0, h1⟩) :=
  ⟨fun _ _ _ h => h ⟨0, h1⟩, fun _ _ _ _ h => h ⟨0, h1⟩⟩

/-- **All three regimes of the trichotomy are realized by the single
`Aggregation` construction.**

1. Arrow-Impossibility: every `S_m`-Pareto+IIA social welfare function
   (`m ≥ 2`, three or more alternatives) occupies it.
2. Arrow-Debreu: the mean-field choice rule occupies it for every
   `β ≤ 1`.
3. Schelling-Ising: the mean-field choice rule occupies it for every
   `β > 1`.

Read with `Trichotomy.trichotomy` (every problem lands in some regime),
this is the genuine unification: three classical results as the three
behaviours of one left Kan extension along the orbit projection. -/
theorem trichotomy_regimes_realized :
    (∀ (m : Nat) (α : Type) [DecidableEq α], 2 ≤ m → AtLeastThree α →
        Nonempty (Profile m α) → ∀ f : SWF m α, SWF.Pareto f → SWF.IIA f →
        IsArrowImpossibilityRegime (profileAction m α) (SWFasChoiceRule f)) ∧
    (∀ (n : Nat) (β : Rat), β ≤ 1 →
        IsArrowDebreuRegime (spinConfigAction n) (magChoiceRule n β)) ∧
    (∀ (n : Nat) (β : Rat), 1 < β →
        IsSchellingIsingRegime (spinConfigAction n) (magChoiceRule n β)) :=
  ⟨fun _ _ _ h2 h3 hNE f hP hI => arrow_impossibility_regime h2 h3 hNE f hP hI,
   fun n _ hβ => paramagnetic_arrow_debreu_regime n hβ,
   fun n _ hβ => schelling_ising_regime n hβ⟩

end UnifiedAggregation
