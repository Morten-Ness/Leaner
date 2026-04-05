import Mathlib

variable {G R S T F : Type*}

variable [Monoid R] [Monoid S] [Monoid T] [FunLike F R S]

variable [MonoidHomClass F R S]

theorem MonoidHom.isLocalHom_comp (g : S →* T) (f : R →* S) [IsLocalHom g]
    [IsLocalHom f] : IsLocalHom (g.comp f) where
  map_nonunit a := IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

-- see note [lower instance priority]

