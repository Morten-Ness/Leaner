import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_two (f : Fin 2 → M) : ∏ i, f i = f 0 * f 1 := by
  simp [Fin.prod_univ_succ]

