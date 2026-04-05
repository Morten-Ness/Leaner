import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem IsPredLimit.lt_sub_one [Sub α] [One α] [PredSubOrder α]
    (hx : IsPredLimit x) (hy : x < y) : x < y - 1 := hx.isPredPrelimit.lt_sub_one hy

