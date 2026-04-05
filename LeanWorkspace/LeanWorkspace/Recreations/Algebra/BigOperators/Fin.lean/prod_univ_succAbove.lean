import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_succAbove (f : Fin (n + 1) → M) (x : Fin (n + 1)) :
    ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i) := by
  rw [univ_succAbove n x, prod_cons, Finset.prod_map, coe_succAboveEmb]

