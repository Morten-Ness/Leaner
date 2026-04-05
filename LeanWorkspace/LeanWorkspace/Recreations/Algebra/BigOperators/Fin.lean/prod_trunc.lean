import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_trunc {a b : ℕ} (f : Fin (a + b) → M) (hf : ∀ j : Fin b, f (natAdd a j) = 1) :
    (∏ i : Fin (a + b), f i) = ∏ i : Fin a, f (castAdd b i) := by
  rw [Fin.prod_univ_add, Fintype.prod_eq_one _ hf, mul_one]

