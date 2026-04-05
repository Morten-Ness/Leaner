import Mathlib

variable {α β : Type*}

variable [Preorder α] [Preorder β] {x y : WithZero α} {a b : α}

theorem lt_ofAdd_iff
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) :
    a < ofAdd b ↔ toAdd (unzero ha) < b := ⟨WithZero.toAdd_unzero_lt_of_lt_ofAdd ha, WithZero.lt_ofAdd_of_toAdd_unzero_lt ha⟩

