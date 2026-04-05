import Mathlib

variable {α G M : Type*}

variable {M : Type*}

variable (f g : ℕ → M) {m n : ℕ}

variable [CommGroup M]

theorem prod_range_succ_div_prod : ((∏ i ∈ range (n + 1), f i) / ∏ i ∈ range n, f i) = f n := div_eq_iff_eq_mul'.mpr <| prod_range_succ f n

