import Mathlib

variable {M N : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

theorem pow_inj_of_not_isUnit {q : M} (hq : ¬IsUnit q)
    (hq' : q ≠ 0) {m n : ℕ} : q ^ m = q ^ n ↔ m = n := (pow_injective_of_not_isUnit hq hq').eq_iff

