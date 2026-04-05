import Mathlib

variable {ι F α β γ δ : Type*}

variable [FunLike F α β]

theorem map_pos_of_ne_one [Group α] [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    [GroupNormClass F α β] (f : F)
    {x : α} (hx : x ≠ 1) : 0 < f x := (apply_nonneg _ _).lt_of_ne <| ((map_ne_zero_iff_ne_one _).2 hx).symm

