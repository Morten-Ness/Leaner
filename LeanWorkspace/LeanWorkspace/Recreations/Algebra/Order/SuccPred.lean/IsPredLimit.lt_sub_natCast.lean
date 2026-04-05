import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem IsPredLimit.lt_sub_natCast [AddCommGroupWithOne α] [PredSubOrder α]
    (hx : IsPredLimit x) (hy : x < y) : ∀ n : ℕ, x < y - n := hx.isPredPrelimit.lt_sub_natCast hy

