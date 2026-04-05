import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem map_zpow [Group α] [DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ) :
    f (g ^ n) = f g ^ n := map_zpow f g n

