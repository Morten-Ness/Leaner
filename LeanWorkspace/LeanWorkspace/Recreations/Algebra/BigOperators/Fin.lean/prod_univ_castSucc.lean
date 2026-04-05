import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_castSucc (f : Fin (n + 1) → M) :
    ∏ i, f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n) := by
  simpa [mul_comm] using Fin.prod_univ_succAbove f (last n)

