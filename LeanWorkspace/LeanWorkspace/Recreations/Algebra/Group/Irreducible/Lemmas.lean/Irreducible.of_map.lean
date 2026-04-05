import Mathlib

variable {F M N : Type*}

variable [Monoid M] [Monoid N] {f : F} {x y : M}

theorem Irreducible.of_map [FunLike F M N] [MonoidHomClass F M N] [IsLocalHom f]
    (hfx : Irreducible (f x)) : Irreducible x where
  not_isUnit hu := hfx.not_isUnit <| hu.map f
  isUnit_or_isUnit := by
    rintro p q rfl; exact (hfx.isUnit_or_isUnit <| map_mul f p q).imp (.of_map f _) (.of_map f _)

