import Mathlib

variable {α β : Type*}

variable [Preorder α] [Preorder β] {x y : WithZero α} {a b : α}

theorem lt_ofAdd_of_toAdd_unzero_lt
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : toAdd (unzero ha) < b) :
    a < ofAdd b := by
  rwa [← coe_unzero ha, coe_lt_coe, ← ofAdd_toAdd (unzero ha), ofAdd_lt]

