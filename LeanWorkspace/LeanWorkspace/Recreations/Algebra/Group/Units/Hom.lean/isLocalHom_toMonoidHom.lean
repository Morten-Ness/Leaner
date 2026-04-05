import Mathlib

variable {G R S T F : Type*}

variable [Monoid R] [Monoid S] [Monoid T] [FunLike F R S]

variable [MonoidHomClass F R S]

theorem isLocalHom_toMonoidHom (f : F) [IsLocalHom f] :
    IsLocalHom (f : R →* S) := ⟨IsLocalHom.map_nonunit (f := f)⟩

