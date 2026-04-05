import Mathlib

variable {σ : Type u} {R : Type v} [CommSemiring R]

theorem cardinalMk_le_max_lift {σ : Type u} {R : Type v} [CommSemiring R] :
    #(MvPolynomial σ R) ≤ lift.{u} #R ⊔ lift.{v} #σ ⊔ ℵ₀ := by
  nontriviality R; cases isEmpty_or_nonempty σ <;> simp

