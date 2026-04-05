import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

variable {M₀ : PresheafOfModules.{v} R₀} {A : Sheaf J AddCommGrpCat.{v}}
  (φ : M₀.presheaf ⟶ A.obj)
  [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]

theorem toSheafify_app_apply (X : Cᵒᵖ) (x : M₀.obj X) :
    ((PresheafOfModules.toSheafify α φ).app X).hom x = φ.app X x := rfl

