import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [SMul α β] [Preorder α] [Preorder β] [Zero α] [PosSMulMono α β] {a : α} {s : Set β}

theorem BddBelow.smul_of_nonneg (hs : BddBelow s) (ha : 0 ≤ a) : BddBelow (a • s) := (monotone_smul_left_of_nonneg ha).map_bddBelow hs

