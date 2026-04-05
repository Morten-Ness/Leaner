import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_def (f : Fin n → M) : ∏ i, f i = ((List.finRange n).map f).prod := by
  rw [← List.ofFn_eq_map, Fin.prod_ofFn]

