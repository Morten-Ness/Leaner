import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

variable {R₀ R : Cᵒᵖ ⥤ RingCat.{u}} (α : R₀ ⟶ R) [Presheaf.IsLocallyInjective J α]
  {M₀ : PresheafOfModules.{v} R₀} {A : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (φ : M₀.presheaf ⟶ A)
  [Presheaf.IsLocallyInjective J φ] (hA : Presheaf.IsSeparated J A)
  {X : C} (r : R.obj (Opposite.op X)) (m : A.obj (Opposite.op X)) {P : Presieve X}
  (r₀ : FamilyOfElements (R₀ ⋙ forget _) P) (m₀ : FamilyOfElements (M₀.presheaf ⋙ forget _) P)

theorem _root_.PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective
    {Y : C} (r₀ r₀' : R₀.obj (Opposite.op Y))
    (m₀ m₀' : M₀.obj (Opposite.op Y))
    (hr₀ : α.app _ r₀ = α.app _ r₀')
    (hm₀ : φ.app _ m₀ = φ.app _ m₀') :
    φ.app _ (r₀ • m₀) = φ.app _ (r₀' • m₀') := by
  apply hA _ (Presheaf.equalizerSieve r₀ r₀' ⊓
      Presheaf.equalizerSieve (F := M₀.presheaf) m₀ m₀')
  · apply J.intersection_covering
    · exact Presheaf.equalizerSieve_mem J α _ _ hr₀
    · exact Presheaf.equalizerSieve_mem J φ _ _ hm₀
  · intro Z g hg
    rw [← NatTrans.naturality_apply (D := Ab), ← NatTrans.naturality_apply (D := Ab)]
    erw [M₀.map_smul, M₀.map_smul, hg.1, hg.2]
    rfl

