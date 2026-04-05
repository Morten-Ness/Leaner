import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

theorem coe_mul_self_eq (s : Submonoid M) : (s : Set M) * s = s := by
  simp

