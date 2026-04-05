import Mathlib

variable {G R S T F : Type*}

variable [Monoid R] [Monoid S] [Monoid T] [FunLike F R S]

variable [MonoidHomClass F R S]

theorem isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (f a) ↔ IsUnit a := ⟨IsLocalHom.map_nonunit a, IsUnit.map f⟩

