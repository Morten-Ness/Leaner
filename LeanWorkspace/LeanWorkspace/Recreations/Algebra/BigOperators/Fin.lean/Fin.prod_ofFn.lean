import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_ofFn (f : Fin n → M) : (List.ofFn f).prod = ∏ i, f i := by
  simp [prod_eq_multiset_prod]

