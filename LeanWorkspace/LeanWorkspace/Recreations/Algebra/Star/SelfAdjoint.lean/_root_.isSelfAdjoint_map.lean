import Mathlib

variable {R A : Type*}

theorem _root_.isSelfAdjoint_map {F R S : Type*} [Star R] [Star S] [FunLike F R S]
    [StarHomClass F R S] [TrivialStar R] (f : F) (x : R) : IsSelfAdjoint (f x) := IsSelfAdjoint.map (IsSelfAdjoint.all x) f

