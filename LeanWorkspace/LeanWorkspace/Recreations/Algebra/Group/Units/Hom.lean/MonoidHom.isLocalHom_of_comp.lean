import Mathlib

variable {G R S T F : Type*}

variable [Monoid R] [Monoid S] [Monoid T] [FunLike F R S]

variable [MonoidHomClass F R S]

theorem MonoidHom.isLocalHom_of_comp (f : R →* S) (g : S →* T) [IsLocalHom (g.comp f)] :
    IsLocalHom f := ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (IsUnit.map ha g)⟩

