import Mathlib

variable {ι : Sort*} {M α : Type*}

theorem pow_smul_le {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : g • a ≤ a) (n : ℕ) : g ^ n • a ≤ a := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ', mul_smul]
    exact (smul_mono_right g hn).trans h

