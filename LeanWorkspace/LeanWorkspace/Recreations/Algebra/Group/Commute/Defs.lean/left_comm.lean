import Mathlib

variable {G M S : Type*}

variable [Semigroup S] {a b c : S}

theorem left_comm (h : Commute a b) (c) : a * (b * c) = b * (a * c) := by
  simp only [← mul_assoc, Commute.eq h]

