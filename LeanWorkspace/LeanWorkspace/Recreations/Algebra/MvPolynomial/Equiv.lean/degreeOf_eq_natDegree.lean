import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem degreeOf_eq_natDegree [DecidableEq σ] (a : σ) (p : MvPolynomial σ R) :
    degreeOf a p =
      (MvPolynomial.optionEquivLeft R {b // b ≠ a} (rename (Equiv.optionSubtypeNe a).symm p)).natDegree := by
  rw [MvPolynomial.natDegree_optionEquivLeft, eq_comm]
  convert degreeOf_rename_of_injective (Equiv.injective (Equiv.optionSubtypeNe a).symm) a
  rw [Equiv.optionSubtypeNe_symm_apply, dif_pos rfl]

