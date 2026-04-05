import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem isUnit_pow_succ_iff : IsUnit (a ^ (n + 1)) ↔ IsUnit a := isUnit_pow_iff n.succ_ne_zero

