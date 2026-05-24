/-
  UnifiedAggregation.Bridge.ArrowImpossibility

  Phase 1a: wire arrow-cat into the Arrow-Impossibility regime.

  arrow-cat proves Arrow's Impossibility Theorem in Geanakoplos form
  (zero `sorry`s):

      theorem ArrowCat.arrow [DecidableEq α]
          (f : SWF m α) (h1 : 0 < m) (h3 : AtLeastThree α)
          (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f) :
          ∃ k : Fin m, SWF.Dictator f k

  and its contrapositive form

      theorem ArrowCat.arrow_contrapositive [DecidableEq α]
          (f : SWF m α) (h1 : 0 < m) (h3 : AtLeastThree α)
          (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f) :
          ¬ SWF.NonDictator f

  This module re-expresses the contrapositive in the unified
  framework's language.  A social welfare function is a choice rule
  from the profile configuration space (`Profile m α`) into the
  outcome space (`StrictPref α`); the symmetric group acts on profiles
  by permuting voter indices; Arrow's theorem becomes the statement
  that no social aggregation simultaneously satisfies Pareto, IIA,
  and non-dictatorship.

  Phase 1a (here): direct restatement of `ArrowCat.arrow_contrapositive`
  in conjunctive non-existence form, proved.

  Phase 1b (next): embed `Profile m α` as a category, `S_m` as a
  `SymmetryGroup`, and the SWF as a `ChoiceRule`, then connect this
  theorem to `IsArrowImpossibilityRegime` via the categorical
  embedding.
-/

import ArrowCat
import UnifiedAggregation.Regimes

set_option autoImplicit false

universe u

namespace UnifiedAggregation.Bridge

open ArrowCat

/-- **Arrow's Impossibility Theorem in conjunctive non-existence
form.**  Under the AtLeastThree-on-`α` and at-least-one-voter
hypotheses, no social welfare function simultaneously satisfies
Pareto efficiency, Independence of Irrelevant Alternatives, and
non-dictatorship.

A direct rewriting of `ArrowCat.arrow_contrapositive`: given an SWF
witnessing the three properties, `arrow_contrapositive` immediately
contradicts the non-dictatorship clause.  Proved in term mode with
no tactic block, since the contradiction is one application deep.

This is Phase 1a's structural connection.  Phase 1b embeds the
Profile category into the unified framework's `(Obj, G, F)` triple
and connects this theorem to the `IsArrowImpossibilityRegime`
predicate via the categorical embedding. -/
theorem arrow_impossibility
    {m : Nat} {α : Type u} [DecidableEq α]
    (h1 : 0 < m) (h3 : AtLeastThree α) :
    ¬ ∃ (f : SWF m α), SWF.Pareto f ∧ SWF.IIA f ∧ SWF.NonDictator f :=
  fun ⟨f, hP, hI, hND⟩ => arrow_contrapositive f h1 h3 hP hI hND

end UnifiedAggregation.Bridge
