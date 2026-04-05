import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem pow_equiv_pow {f1 f2 : CauSeq β abv} (hf : f1 ≈ f2) (n : ℕ) : f1 ^ n ≈ f2 ^ n := by
  induction n with
  | zero => simp only [pow_zero, Setoid.refl]
  | succ n ih => simpa only [pow_succ'] using CauSeq.mul_equiv_mul hf ih

