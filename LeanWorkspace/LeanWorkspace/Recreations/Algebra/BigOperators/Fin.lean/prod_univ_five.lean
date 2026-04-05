import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_five (f : Fin 5 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_four]
  rfl

