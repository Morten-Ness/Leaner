import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (s : Subsemiring R)

theorem map_map (g : S →+* T) (f : R →+* S) : (s.map f).map g = s.map (g.comp f) := SetLike.coe_injective <| Set.image_image _ _ _

