import Mathlib

variable {ι : Sort*} {M α : Type*}

theorem smul_le_smul_left [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) {a b : α} (h : a ≤ b) :
    m • a ≤ m • b := smul_mono_right _ h

