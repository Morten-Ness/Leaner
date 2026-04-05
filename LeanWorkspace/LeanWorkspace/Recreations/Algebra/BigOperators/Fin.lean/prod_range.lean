import Mathlib

variable {ι M : Type*}

theorem prod_range [CommMonoid M] {n : ℕ} (f : ℕ → M) :
    ∏ i ∈ Finset.range n, f i = ∏ i : Fin n, f i := (Fin.prod_univ_eq_prod_range _ _).symm

