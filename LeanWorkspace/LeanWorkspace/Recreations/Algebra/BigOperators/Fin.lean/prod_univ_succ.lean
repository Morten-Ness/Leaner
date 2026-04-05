import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_succ (f : Fin (n + 1) → M) :
    ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ := Fin.prod_univ_succAbove f 0

