/-
  UnifiedAggregation.Bridge.ArrowDebreu

  Phase 2 (T1): symbolic Arrow-Debreu via S_m symmetry on allocations.

  We model a symmetric exchange economy with m consumers as the
  discrete category on natural-number-valued allocations
  `Fin m → Nat`.  The S_m action permutes consumer labels.  The
  Arrow-Debreu regime witness: any S_m-equivariant (anonymous)
  allocation is uniform across consumers, hence determined by its
  value at a single index, hence unique up to that one degree of
  freedom.

  This is the symbolic form of "unique equilibrium under convex
  symmetric preferences": the classical Arrow-Debreu existence
  theorem via Kakutani fixed point requires real-valued machinery
  (Mathlib); the structural uniqueness claim captured here is the
  load-bearing shadow of that result.
-/

import UnifiedAggregation.Discrete
import UnifiedAggregation.SymmetricGroup
import UnifiedAggregation.Aggregation
import UnifiedAggregation.Regimes
import UnifiedAggregation.FunctorExt
import ArrowCat

set_option autoImplicit false

namespace UnifiedAggregation.Bridge

open ArrowCat
open ArrowCat.StrictPref
open CompCatTheory

/-! ## Allocations and anonymity -/

/-- An allocation: assigns a non-negative integer quantity to each
of `m` consumers. -/
def Allocation (m : Nat) : Type := Fin m → Nat

/-- An allocation is *anonymous* if it is invariant under all
permutations of consumer indices.  This is the framework's `S_m`
equivariance condition specialized to the Arrow-Debreu setting. -/
def Allocation.IsAnonymous {m : Nat} (a : Allocation m) : Prop :=
  ∀ σ : Perm m, (fun i => a (σ.toFun i)) = a

/-- **Anonymous implies uniform**: any anonymous allocation gives the
same quantity to every consumer.  Proved by swapping consumer 0 with
an arbitrary consumer `i` and applying the anonymity hypothesis at
index 0.

This is the structural content of "unique equilibrium under
symmetric preferences": the `S_m` symmetry of the economy forces the
allocation to a single canonical form (the equal split). -/
theorem Allocation.anonymous_eq_at_zero {m : Nat} (hm : 0 < m)
    (a : Allocation m) (h_anon : a.IsAnonymous) (i : Fin m) :
    a i = a ⟨0, hm⟩ := by
  by_cases h_eq : i = ⟨0, hm⟩
  · rw [h_eq]
  · let σ : Perm m := {
      toFun := swapMap ⟨0, hm⟩ i,
      invFun := swapMap ⟨0, hm⟩ i,
      left_inv := swapMap_involution ⟨0, hm⟩ i,
      right_inv := swapMap_involution ⟨0, hm⟩ i }
    have h_σ : σ.toFun ⟨0, hm⟩ = i := swapMap_at_a ⟨0, hm⟩ i
    have h_anon_zero : a (σ.toFun ⟨0, hm⟩) = a ⟨0, hm⟩ :=
      congrFun (h_anon σ) ⟨0, hm⟩
    rw [h_σ] at h_anon_zero
    exact h_anon_zero

/-- **Arrow-Debreu uniqueness (symbolic, headline)**: two anonymous
allocations that agree at consumer 0 are equal everywhere.

This is the load-bearing uniqueness claim for the Arrow-Debreu
regime: under the symmetric `S_m` structure, the equilibrium is
determined by a single parameter (the per-consumer share), hence
unique.  The framework's `IsArrowDebreuRegime` predicate (uniqueness
of `Lan_p F`) is structurally witnessed by anonymous allocations
under the `allocationAction` below. -/
theorem arrow_debreu_uniqueness {m : Nat} (hm : 0 < m)
    (a b : Allocation m)
    (ha : a.IsAnonymous) (hb : b.IsAnonymous)
    (h_zero : a ⟨0, hm⟩ = b ⟨0, hm⟩) :
    a = b := by
  funext i
  rw [Allocation.anonymous_eq_at_zero hm a ha i,
      Allocation.anonymous_eq_at_zero hm b hb i, h_zero]

/-! ## Categorical embedding

The Arrow-Debreu setting enters the unified framework as the discrete
category on allocations with the `S_m` action permuting consumer
labels.  Mirrors the `profileAction` construction of Phase 1a. -/

/-- The configuration category for Arrow-Debreu: discrete category
on `Allocation m`. -/
abbrev AllocationCat (m : Nat) : Type := Discrete (Allocation m)

/-- Endofunctor on `AllocationCat m` induced by a permutation of
consumer indices.  Action convention `act σ a = a ∘ σ.toFun`, same
as `actByPerm` in Phase 1a (so the composition formula matches
`UnifiedAggregation.ConfigSpace.GAction`'s `act (g.comp h) =
act h ⋙ act g`). -/
def actByPermAlloc {m : Nat} (σ : Perm m) :
    AllocationCat m ⥤ AllocationCat m :=
  discreteFunctor (fun a => fun i => a (σ.toFun i))

/-- The `S_m` action on `Allocation m`, lifted to a `GAction` on
`AllocationCat m`.  Same recipe as `profileAction`: `act_one` and
`act_mul` close via `Functor.ext` + `funext` + `heq_of_eq` + match
on `DiscreteHom.id`. -/
def allocationAction (m : Nat) :
    GAction (SymmetricGroup m) (AllocationCat m) where
  act := actByPermAlloc
  act_one :=
    UnifiedAggregation.Functor.ext
      (funext (fun _ => rfl))
      (heq_of_eq (funext (fun _ => funext (fun _ => funext (fun h =>
        match h with
        | DiscreteHom.id _ => rfl)))))
  act_mul _ _ :=
    UnifiedAggregation.Functor.ext
      (funext (fun _ => rfl))
      (heq_of_eq (funext (fun _ => funext (fun _ => funext (fun h =>
        match h with
        | DiscreteHom.id _ => rfl)))))

end UnifiedAggregation.Bridge
