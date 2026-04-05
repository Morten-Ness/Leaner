import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Set β} {a : α}

theorem BddBelow.smul_of_nonpos (ha : a ≤ 0) (hs : BddBelow s) : BddAbove (a • s) := (antitone_smul_left ha).map_bddBelow hs

