import Mathlib

variable {α G M : Type*}

variable {M : Type*}

variable (f g : ℕ → M) {m n : ℕ}

variable [CommGroup M]

theorem prod_Ico_div_bot (hmn : m < n) : (∏ i ∈ Ico m n, f i) / f m = ∏ i ∈ Ico (m + 1) n, f i := div_eq_iff_eq_mul'.mpr <| prod_eq_prod_Ico_succ_bot hmn _

