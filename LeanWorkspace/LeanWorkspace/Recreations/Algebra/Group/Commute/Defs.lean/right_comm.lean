import Mathlib

variable {G M S : Type*}

variable [Semigroup S] {a b c : S}

theorem right_comm (h : Commute b c) (a : S) : a * b * c = a * c * b := by
  simp only [mul_assoc, Commute.eq h]

