import Mathlib

variable {G R S T F : Type*}

variable [Monoid R] [Monoid S] [Monoid T] [FunLike F R S]

variable [MonoidHomClass F R S]

theorem isLocalHom_of_leftInverse [FunLike G S R] [MonoidHomClass G S R]
    {f : F} (g : G) (hfg : Function.LeftInverse g f) : IsLocalHom f where
  map_nonunit a ha := by rwa [isUnit_map_of_leftInverse g hfg] at ha

