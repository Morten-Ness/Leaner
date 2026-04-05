import Mathlib

variable {F α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [LinearOrder β] [IsStrictOrderedRing β] [FloorRing α] [FloorRing β]

variable [FunLike F α β] [RingHomClass F α β] {a : α} {b : β}

theorem map_round (f : F) (hf : StrictMono f) (a : α) : round (f a) = round a := by
  simp_rw [round_eq, ← map_floor _ hf, map_add, one_div, map_inv₀, map_ofNat]

