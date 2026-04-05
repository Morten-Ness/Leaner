import Mathlib

variable {α β : Type*}

variable [Preorder α] [Preorder β] {x y : WithZero α} {a b : α}

theorem toAdd_unzero_le_of_lt_ofAdd
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : a ≤ ofAdd b) :
    toAdd (unzero ha) ≤ b := by
  rwa [← coe_unzero ha, coe_le_coe, ← toAdd_le, toAdd_ofAdd] at h

