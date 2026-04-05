import Mathlib

variable {σ R : Type u} [CommSemiring R]

theorem cardinalMk_eq_max [Nonempty σ] [Nontrivial R] : #(MvPolynomial σ R) = #R ⊔ #σ ⊔ ℵ₀ := by
  simp [sup_assoc]

