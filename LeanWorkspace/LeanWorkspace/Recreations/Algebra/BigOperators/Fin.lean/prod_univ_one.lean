import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_one (f : Fin 1 → M) : ∏ i, f i = f 0 := by simp

