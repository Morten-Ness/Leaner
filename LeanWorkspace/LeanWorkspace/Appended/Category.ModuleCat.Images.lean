import Mathlib

section

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem image.fac : ModuleCat.factorThruImage f ≫ ModuleCat.image.ι f = f := rfl

attribute [local simp] ModuleCat.image.fac

end

section

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem image.lift_fac (F' : MonoFactorisation f) : ModuleCat.image.lift F' ≫ F'.m = ModuleCat.image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl

end

section

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem imageIsoRange_hom_subtype {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (ModuleCat.imageIsoRange f).hom ≫ ModuleCat.ofHom (LinearMap.range f.hom).subtype = Limits.image.ι f := by
  rw [← ModuleCat.imageIsoRange_inv_image_ι f, Iso.hom_inv_id_assoc]

end
