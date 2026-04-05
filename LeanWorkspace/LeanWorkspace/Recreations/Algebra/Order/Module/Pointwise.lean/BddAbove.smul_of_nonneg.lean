import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [SMul α β] [Preorder α] [Preorder β] [Zero α] [PosSMulMono α β] {a : α} {s : Set β}

theorem BddAbove.smul_of_nonneg (hs : BddAbove s) (ha : 0 ≤ a) : BddAbove (a • s) := (monotone_smul_left_of_nonneg ha).map_bddAbove hs

