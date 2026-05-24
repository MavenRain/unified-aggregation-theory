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
  by permuting voter indices.  Arrow's theorem becomes the statement
  that no social aggregation simultaneously satisfies Pareto, IIA, and
  non-dictatorship.

  Phase 1a-precursor: direct restatement of `ArrowCat.arrow_contrapositive`
  in conjunctive non-existence form, proved.

  Phase 1a (here, in progress): categorical embedding pieces.
    - `ProfileCat m α`: the discrete category on profiles
    - `actByPerm`: the endofunctor induced by a permutation of voters
    - `profileAction`: the `S_m` action assembled as a `GAction`

  Phase 1a (remaining): the SWF-as-`ChoiceRule` embedding plus the
  connecting theorem to `IsArrowImpossibilityRegime`.  This requires
  refining `IsArrowImpossibilityRegime` (or adding a constraint-
  parameterized companion) to capture Pareto + IIA + non-dictator as
  the failure conditions.
-/

import ArrowCat
import UnifiedAggregation.Regimes
import UnifiedAggregation.Discrete
import UnifiedAggregation.SymmetricGroup
import UnifiedAggregation.FunctorExt

set_option autoImplicit false

universe u

namespace UnifiedAggregation.Bridge

open ArrowCat
open CompCatTheory

/-- **Arrow's Impossibility Theorem in conjunctive non-existence
form.**  Under the AtLeastThree-on-`α` and at-least-one-voter
hypotheses, no social welfare function simultaneously satisfies
Pareto efficiency, Independence of Irrelevant Alternatives, and
non-dictatorship.

A direct rewriting of `ArrowCat.arrow_contrapositive`: given an SWF
witnessing the three properties, `arrow_contrapositive` immediately
contradicts the non-dictatorship clause.  Proved in term mode with
no tactic block, since the contradiction is one application deep. -/
theorem arrow_impossibility
    {m : Nat} {α : Type u} [DecidableEq α]
    (h1 : 0 < m) (h3 : AtLeastThree α) :
    ¬ ∃ (f : SWF m α), SWF.Pareto f ∧ SWF.IIA f ∧ SWF.NonDictator f :=
  fun ⟨f, hP, hI, hND⟩ => arrow_contrapositive f h1 h3 hP hI hND

/-! ## Categorical embedding for Phase 1a

`Profile m α` enters the unified framework as a *discrete* category:
the only morphisms are identities, since the social-choice problem
does not naturally distinguish "transformations of profiles" beyond
equality.  `S_m` acts on this category by permuting voter indices. -/

/-- The configuration category for Arrow's setting: the discrete
category on `Profile m α`. -/
abbrev ProfileCat (m : Nat) (α : Type u) : Type u :=
  Discrete (Profile m α)

/-- The endofunctor on `ProfileCat m α` induced by a permutation of
voters.  Acts on a profile `p` by `fun i => p (σ.toFun i)`: the i-th
voter in the resulting profile inherits voter `σ.toFun i`'s
preferences from `p`.

The convention `p ∘ σ.toFun` (rather than `p ∘ σ.invFun`) is chosen
so that the action composes to match `act (g.comp h) = act h ⋙ act g`,
the formula encoded in `UnifiedAggregation.ConfigSpace.GAction`. -/
def actByPerm {m : Nat} {α : Type u} (σ : Perm m) :
    ProfileCat m α ⥤ ProfileCat m α :=
  discreteFunctor (fun p => fun i => p (σ.toFun i))

/-- The `S_m` action on `Profile m α`.  Each permutation lifts to an
endofunctor on `ProfileCat m α` via `actByPerm`.

Both `act_one` and `act_mul` close via the same recipe: apply
`UnifiedAggregation.Functor.ext`, prove the obj-equality by
`funext (fun _ => rfl)` (Discrete structure eta on the wrapper), and
prove the map-equality by `heq_of_eq` + nested `funext` + case
analysis on the single `.id` constructor of `DiscreteHom`.  No tactic
blocks; pure term mode. -/
def profileAction (m : Nat) (α : Type u) :
    GAction (SymmetricGroup m) (ProfileCat m α) where
  act := actByPerm
  act_one :=
    UnifiedAggregation.Functor.ext
      (funext (fun _ => rfl))
      (heq_of_eq (funext (fun _ => funext (fun _ => funext (fun h =>
        match h with
        | .id _ => rfl)))))
  act_mul _ _ :=
    UnifiedAggregation.Functor.ext
      (funext (fun _ => rfl))
      (heq_of_eq (funext (fun _ => funext (fun _ => funext (fun h =>
        match h with
        | .id _ => rfl)))))

/-- A *social welfare function* lifts to a functor between the discrete
profile category and the discrete strict-preference category.  This is
the `ChoiceRule` of the unified framework instantiated to Arrow's
social-choice setting: the SWF's object map is its function action,
and discrete morphisms are mapped to identities (no nontrivial
naturality to preserve, since the source category has only identity
arrows). -/
def SWFasChoiceRule {m : Nat} {α : Type u} (f : SWF m α) :
    ProfileCat m α ⥤ Discrete (StrictPref α) :=
  discreteFunctor f

end UnifiedAggregation.Bridge
