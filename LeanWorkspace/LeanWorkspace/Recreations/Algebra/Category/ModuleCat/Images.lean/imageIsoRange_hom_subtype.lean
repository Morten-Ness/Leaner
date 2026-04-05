import Mathlib

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem imageIsoRange_hom_subtype {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (ModuleCat.imageIsoRange f).hom ≫ ModuleCat.ofHom (LinearMap.range f.hom).subtype = Limits.image.ι f := by
  rw [← ModuleCat.imageIsoRange_inv_image_ι f, Iso.hom_inv_id_assoc]

