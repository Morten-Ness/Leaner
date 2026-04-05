import Mathlib

variable {M N S : Type*}

variable [Monoid M] {a : M}

theorem pow_eq (h : IsIdempotentElem a) {n : ℕ} (hn : n ≠ 0) : a ^ n = a := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  exact IsIdempotentElem.pow_succ_eq h _

