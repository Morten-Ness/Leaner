import Mathlib

variable {σ : Type u} {R : Type v} [CommSemiring R]

theorem cardinalMk_eq_max_lift [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = lift.{u} #R ⊔ lift.{v} #σ ⊔ ℵ₀ := by simp [sup_assoc]

-- We want this to have higher priority than `AddMonoidAlgebra.cardinalMk_eq_lift_of_fintype`.

