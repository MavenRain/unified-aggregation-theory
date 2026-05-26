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
open ArrowCat.StrictPref
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

/-! ## Connection theorems

The framework's `S_m` action on profiles encodes anonymity (an SWF
respects the action iff it treats voters interchangeably).  These
connection theorems make the framework load-bearing: results that
need the GAction structure, not just arrow-cat's classical
statement. -/

/-- *Weak connection*: Arrow's Impossibility Theorem restated with
the framework's `Aggregation` type appearing in the conclusion.

The `Aggregation` clause is unused for the contradiction (the SWF
hypotheses alone suffice via `arrow_impossibility`), so this is a
"framework-typed" restatement rather than a framework-driven one. -/
theorem arrow_impossibility_in_framework
    {m : Nat} {α : Type u} [DecidableEq α]
    (h1 : 0 < m) (h3 : AtLeastThree α) :
    ¬ ∃ (f : SWF m α),
        SWF.Pareto f ∧ SWF.IIA f ∧ SWF.NonDictator f ∧
        Nonempty (Aggregation (profileAction m α) (SWFasChoiceRule f)) :=
  fun ⟨f, hP, hI, hND, _⟩ => arrow_impossibility h1 h3 ⟨f, hP, hI, hND⟩

/-- *Equivariance transfer*: an anonymous SWF transfers the dictator
role between any two voters connected by a permutation.  If `k` is a
dictator and `σ` maps `k` to `k'`, then `k'` is also a dictator.

This is the load-bearing piece for the strong connection theorem:
combined with Arrow's theorem (which produces a dictator) and the
ability to construct permutations between distinct voters (for
`m ≥ 2`), it shows that anonymity is incompatible with
Pareto + IIA over 3+ alternatives. -/
theorem equivariant_dictator_transfer
    {m : Nat} {α : Type u}
    (f : SWF m α)
    (h_equiv : ∀ (σ : Perm m) (p : Profile m α),
        f (fun i => p (σ.toFun i)) = f p)
    {k k' : Fin m} {σ : Perm m} (h_σ : σ.toFun k = k')
    (h_dict : SWF.Dictator f k) :
    SWF.Dictator f k' := by
  -- exception: standard tactics (intro/let/have/exact + rewrite via ▸)
  -- since kan-tactics has no funext-style alternative for the rewrite.
  intro p' a b h_pref
  let p_new : Profile m α := fun i => p' (σ.toFun i)
  have h_pn_k : p_new k = p' k' := by
    show p' (σ.toFun k) = p' k'
    rw [h_σ]
  have h_pn_pref : (p_new k).pref a b := h_pn_k ▸ h_pref
  have h_f_pn : (f p_new).pref a b := h_dict p_new a b h_pn_pref
  have h_eq : f p_new = f p' := h_equiv σ p'
  exact h_eq ▸ h_f_pn

/-- *Every voter is a dictator under equivariance*: if an SWF is
equivariant under all permutations and the `S_m` action is transitive
on voters (which it always is for the full symmetric group, but is
left as a hypothesis here to avoid the swap-permutation construction),
then Arrow's dictator is universal.

Proved by combining `arrow` (which gives some dictator `k₀`) with
`equivariant_dictator_transfer` (which transfers the role to any `k`
via the transitivity witness). -/
theorem all_voters_dictator_under_equivariance
    {m : Nat} {α : Type u} [DecidableEq α]
    (h1 : 0 < m) (h3 : AtLeastThree α)
    (f : SWF m α)
    (h_equiv : ∀ (σ : Perm m) (p : Profile m α),
        f (fun i => p (σ.toFun i)) = f p)
    (hP : SWF.Pareto f) (hI : SWF.IIA f)
    (h_trans : ∀ (k k' : Fin m), ∃ σ : Perm m, σ.toFun k = k') :
    ∀ k : Fin m, SWF.Dictator f k := by
  intro k
  obtain ⟨k₀, hD⟩ := arrow f h1 h3 hP hI
  obtain ⟨σ, hσ⟩ := h_trans k₀ k
  exact equivariant_dictator_transfer f h_equiv hσ hD

/-- *Two distinct dictators are contradictory*: if any two distinct
voters are both dictators of an SWF, a disagreement profile (where
the two voters rank `a`, `b` oppositely) plus the dictator hypothesis
forces `(f p).pref a b ∧ (f p).pref b a`, violating asymmetry.

Profile construction: take any base profile `p₀`, then `moveBToBottom b`
on voter `k₁` (making `a > b` for `k₁`) and `moveBToBottom a` on
voter `k₂` (making `b > a` for `k₂`).  Uses arrow-cat's
`StrictPref.moveBToBottom` plus `moveBToBottom_pref_other_b`. -/
theorem no_two_dictators
    {m : Nat} {α : Type u}
    (_h2 : 2 ≤ m) (h3 : AtLeastThree α)
    (hNE : Nonempty (Profile m α))
    (f : SWF m α)
    {k₁ k₂ : Fin m} (h_ne : k₁ ≠ k₂)
    (hD₁ : SWF.Dictator f k₁) (hD₂ : SWF.Dictator f k₂) :
    False := by
  obtain ⟨a, b, _, hab, _, _⟩ := h3
  have h_ba : b ≠ a := Ne.symm hab
  let p₀ := Classical.choice hNE
  -- Profile: voter k₁ has b at bottom (so a > b), voter k₂ has a at
  -- bottom (so b > a), others keep p₀'s preference.
  let p : Profile m α := fun i =>
    if i = k₁ then (p₀ k₁).moveBToBottom b
    else if i = k₂ then (p₀ k₂).moveBToBottom a
    else p₀ i
  have h_pk1 : p k₁ = (p₀ k₁).moveBToBottom b := if_pos rfl
  have h_pk2 : p k₂ = (p₀ k₂).moveBToBottom a := by
    show (if k₂ = k₁ then (p₀ k₁).moveBToBottom b
          else if k₂ = k₂ then (p₀ k₂).moveBToBottom a
          else p₀ k₂) = _
    rw [if_neg (Ne.symm h_ne), if_pos rfl]
  have hPref_k1 : (p k₁).pref a b :=
    h_pk1 ▸ moveBToBottom_pref_other_b _ hab
  have hPref_k2 : (p k₂).pref b a :=
    h_pk2 ▸ moveBToBottom_pref_other_b _ h_ba
  have h_fab : (f p).pref a b := hD₁ p a b hPref_k1
  have h_fba : (f p).pref b a := hD₂ p b a hPref_k2
  exact (f p).asym a b h_fab h_fba

/-- *Strong connection theorem* — the framework's `S_m` action is
load-bearing: no SWF over `m ≥ 2` voters and 3+ alternatives can
simultaneously be `S_m`-equivariant and satisfy Pareto + IIA.

Proof structure (modulo two internal sorries):
1. Arrow gives a dictator `k₀`.
2. Equivariance + transitivity of `S_m` (sorry: needs the swap
   permutation construction) makes every voter a dictator.
3. Two distinct dictators give a disagreement-profile contradiction
   (sorry: `no_two_dictators`).

This is the headline theorem that justifies the categorical framing:
arrow-cat's classical statement allows dictators, but the unified
framework's `S_m` action requires anonymity, which Arrow's hypotheses
rule out for `m ≥ 2`. -/
theorem no_equivariant_constrained_swf
    {m : Nat} {α : Type u} [DecidableEq α]
    (h2 : 2 ≤ m) (h3 : AtLeastThree α)
    (hNE : Nonempty (Profile m α)) :
    ¬ ∃ (f : SWF m α),
        (∀ (σ : Perm m) (p : Profile m α),
            f (fun i => p (σ.toFun i)) = f p) ∧
        SWF.Pareto f ∧ SWF.IIA f := by
  intro ⟨f, h_equiv, hP, hI⟩
  -- Transitivity of S_m action on Fin m, using arrow-cat's swapMap
  -- to build the swap permutation when k ≠ k'.
  have h_trans : ∀ (k k' : Fin m), ∃ σ : Perm m, σ.toFun k = k' := fun k k' =>
    if h : k = k' then
      ⟨Perm.id m, h⟩
    else
      ⟨{ toFun := swapMap k k'
         invFun := swapMap k k'
         left_inv := swapMap_involution k k'
         right_inv := swapMap_involution k k' },
        swapMap_at_a k k'⟩
  -- Every voter is a dictator
  have h_all : ∀ k : Fin m, SWF.Dictator f k :=
    all_voters_dictator_under_equivariance
      (Nat.lt_of_lt_of_le Nat.zero_lt_two h2) h3 f h_equiv hP hI h_trans
  -- For m ≥ 2 there are two distinct voters: ⟨0, _⟩ and ⟨1, _⟩
  let k₀ : Fin m := ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two h2⟩
  let k₁ : Fin m := ⟨1, h2⟩
  have hk0_ne_k1 : k₀ ≠ k₁ := by
    intro heq
    have : (0 : Nat) = 1 := congrArg Fin.val heq
    exact absurd this (by decide)
  exact no_two_dictators h2 h3 hNE f hk0_ne_k1 (h_all k₀) (h_all k₁)

end UnifiedAggregation.Bridge
