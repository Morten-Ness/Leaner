import Mathlib

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem imageIsoRange_inv_image_ι {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (ModuleCat.imageIsoRange f).inv ≫ Limits.image.ι f = ModuleCat.ofHom (LinearMap.range f.hom).subtype := IsImage.isoExt_inv_m _ _

