/-
  UnifiedAggregation.SymmetricGroup

  The symmetric group S_n on `Fin n`, constructed without Mathlib.
  This is the anonymity-bearing group for both Arrow's social-choice
  setting (`Bridge.ArrowImpossibility`) and the symbolic Arrow-Debreu
  setting (`Bridge.ArrowDebreu`): S_m acts on `Profile m α` by
  permuting voter indices, and on `Allocation m` by permuting
  consumer indices.  In both cases anonymity is the S_m-equivariance
  of the choice rule, and `arrow-cat`'s `NonDictator` hypothesis
  corresponds to non-equivariance under this action.

  Candidate for upstreaming to `comp-cat-theory` or to a dedicated
  group-theory reservoir; kept local to avoid cross-repo churn.
-/

import UnifiedAggregation.ConfigSpace

set_option autoImplicit false

namespace UnifiedAggregation

/-- A *permutation* of `Fin n`: a bijection on the index set with
explicit inverse data and the two round-trip identities.  Explicit
`invFun` data (rather than a `Function.Bijective` proof) makes
`Perm.inv` definable without classical choice and makes the
inverse-pair laws (`mul_inv`, `inv_mul`) provable by `funext` on the
stored identities. -/
structure Perm (n : Nat) where
  toFun     : Fin n → Fin n
  invFun    : Fin n → Fin n
  left_inv  : ∀ x, invFun (toFun x) = x
  right_inv : ∀ x, toFun (invFun x) = x

namespace Perm

/-- The identity permutation. -/
def id (n : Nat) : Perm n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

/-- Composition: `σ.comp τ` applies `σ` first, then `τ`.  The inverse
is the reverse composition of the component inverses; the round-trip
identities chain via `congrArg` and `.trans`. -/
def comp {n : Nat} (σ τ : Perm n) : Perm n where
  toFun x := τ.toFun (σ.toFun x)
  invFun x := σ.invFun (τ.invFun x)
  left_inv x :=
    (congrArg σ.invFun (τ.left_inv (σ.toFun x))).trans (σ.left_inv x)
  right_inv x :=
    (congrArg τ.toFun (σ.right_inv (τ.invFun x))).trans (τ.right_inv x)

/-- Inverse: swap the to-function and the inverse function; the
round-trip identities swap correspondingly. -/
def inv {n : Nat} (σ : Perm n) : Perm n where
  toFun := σ.invFun
  invFun := σ.toFun
  left_inv := σ.right_inv
  right_inv := σ.left_inv

/-- Two permutations are equal iff their `toFun` and `invFun` fields
agree.  The proof fields are propositionally equal by Lean's
definitional proof irrelevance on `Prop`-valued struct fields. -/
theorem ext {n : Nat} : ∀ {σ τ : Perm n},
    σ.toFun = τ.toFun → σ.invFun = τ.invFun → σ = τ
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl, rfl => rfl

/-- Identity is a left unit for composition (definitional). -/
theorem one_mul {n : Nat} (σ : Perm n) : (id n).comp σ = σ := rfl

/-- Identity is a right unit for composition (definitional). -/
theorem mul_one {n : Nat} (σ : Perm n) : σ.comp (id n) = σ := rfl

/-- Composition is associative (definitional). -/
theorem mul_assoc {n : Nat} (σ τ ρ : Perm n) :
    (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := rfl

/-- Right-inverse law: `σ.comp σ.inv = id`. -/
theorem mul_inv {n : Nat} (σ : Perm n) : σ.comp σ.inv = id n :=
  ext (funext σ.left_inv) (funext σ.left_inv)

/-- Left-inverse law: `σ.inv.comp σ = id`. -/
theorem inv_mul {n : Nat} (σ : Perm n) : σ.inv.comp σ = id n :=
  ext (funext σ.right_inv) (funext σ.right_inv)

end Perm

/-- The symmetric group on `Fin n` as a `SymmetryGroup`.  Used by the
Phase 1a categorical embedding as the anonymity-bearing group acting
on `Profile n α` by permuting voter indices. -/
def SymmetricGroup (n : Nat) : SymmetryGroup.{0} where
  carrier   := Perm n
  one       := Perm.id n
  mul       := Perm.comp
  inv       := Perm.inv
  one_mul   := Perm.one_mul
  mul_one   := Perm.mul_one
  mul_assoc := Perm.mul_assoc
  mul_inv   := Perm.mul_inv
  inv_mul   := Perm.inv_mul

end UnifiedAggregation
