import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_add {a b : ℕ} (f : Fin (a + b) → M) :
    (∏ i : Fin (a + b), f i) = (∏ i : Fin a, f (castAdd b i)) * ∏ i : Fin b, f (natAdd a i) := by
  rw [Fintype.prod_equiv finSumFinEquiv.symm f fun i => f (finSumFinEquiv.toFun i)]
  · apply Fintype.prod_sum_type
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]

