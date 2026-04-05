import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOne M] [MulOne N]

variable [FunLike F M N]

variable [FunLike F G H]

theorem map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) :
    ∀ a b, f (a / b) = f a / f b := map_div' _ <| map_inv f

