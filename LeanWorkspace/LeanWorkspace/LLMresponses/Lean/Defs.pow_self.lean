import Mathlib

variable {G M S : Type*}

variable [Monoid M] {a b : M}

theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a := by
  simpa [Commute.eq] using (Commute.pow_right (Commute.refl a) n).symm
