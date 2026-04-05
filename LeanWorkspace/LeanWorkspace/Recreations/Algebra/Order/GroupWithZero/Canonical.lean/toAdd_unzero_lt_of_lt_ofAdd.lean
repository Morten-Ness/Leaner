import Mathlib

variable {α β : Type*}

variable [Preorder α] [Preorder β] {x y : WithZero α} {a b : α}

theorem toAdd_unzero_lt_of_lt_ofAdd
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : a < ofAdd b) :
    toAdd (unzero ha) < b := by
  rwa [← coe_unzero ha, coe_lt_coe, ← toAdd_lt, toAdd_ofAdd] at h

