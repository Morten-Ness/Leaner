import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem map_div [Group α] [DivisionMonoid β] (f : α →* β) (g h : α) :
    f (g / h) = f g / f h := map_div f g h

