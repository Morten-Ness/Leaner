import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_three (f : Fin 3 → M) : ∏ i, f i = f 0 * f 1 * f 2 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_two]
  rfl

