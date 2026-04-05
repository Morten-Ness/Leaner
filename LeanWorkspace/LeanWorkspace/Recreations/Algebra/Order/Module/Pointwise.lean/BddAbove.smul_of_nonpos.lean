import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Set β} {a : α}

theorem BddAbove.smul_of_nonpos (ha : a ≤ 0) (hs : BddAbove s) : BddBelow (a • s) := (antitone_smul_left ha).map_bddAbove hs

