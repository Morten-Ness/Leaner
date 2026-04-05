import Mathlib

variable {R A : Type*}

theorem map {F R S : Type*} [Star R] [Star S] [FunLike F R S] [StarHomClass F R S]
    {x : R} (hx : IsSelfAdjoint x) (f : F) : IsSelfAdjoint (f x) := show star (f x) = f x from map_star f x ▸ congr_arg f hx

