import Mathlib

variable {ι : Sort*} {M α : Type*}

theorem le_pow_smul {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : a ≤ g • a) (n : ℕ) : a ≤ g ^ n • a := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ', mul_smul]
    exact h.trans (smul_mono_right g hn)

