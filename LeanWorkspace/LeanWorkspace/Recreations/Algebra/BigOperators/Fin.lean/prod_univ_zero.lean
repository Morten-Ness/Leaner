import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_zero (f : Fin 0 → M) : ∏ i, f i = 1 := rfl

