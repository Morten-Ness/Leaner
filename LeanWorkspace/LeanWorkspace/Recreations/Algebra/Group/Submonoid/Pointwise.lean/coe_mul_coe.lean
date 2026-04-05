import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

theorem coe_mul_coe [SetLike S M] [SubmonoidClass S M] (H : S) : H * H = (H : Set M) := by
  aesop (add simp mem_mul)

