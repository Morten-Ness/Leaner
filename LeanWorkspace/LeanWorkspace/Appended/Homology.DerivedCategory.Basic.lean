import Mathlib

section

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

theorem Q_map_eq_of_homotopy {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g := HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy h

end

section

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

theorem isIso_Q_map_iff_quasiIso {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (DerivedCategory.Q.map φ) ↔ QuasiIso φ := by
  apply HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso

end

section

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

variable {C} {K L : CochainComplex C ℤ} (φ : K ⟶ L)

theorem mappingCocone_triangle_distinguished :
    DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle φ) ∈ distTriang _ := by
  rw [rotate_distinguished_triangle]
  exact isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished φ) _
    (DerivedCategory.Q.mapTriangleRotateIso.app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso (mappingCocone.rotateTriangleIso φ))

end

section

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

variable {C} {K L : CochainComplex C ℤ} (φ : K ⟶ L)

theorem mappingCone_triangle_distinguished :
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle φ) ∈ distTriang _ := by
  rw [DerivedCategory.mem_distTriang_iff]
  exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

end

section

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

theorem mem_distTriang_iff (T : Triangle (DerivedCategory C)) :
    (T ∈ distTriang (DerivedCategory C)) ↔ ∃ (X Y : CochainComplex C ℤ) (f : X ⟶ Y),
      Nonempty (T ≅ DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)) := by
  constructor
  · rintro ⟨T', e, ⟨X, Y, f, ⟨e'⟩⟩⟩
    refine ⟨_, _, f, ⟨?_⟩⟩
    exact e ≪≫ DerivedCategory.Qh.mapTriangle.mapIso e' ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) DerivedCategory.Qh).symm.app _ ≪≫
      (Functor.mapTriangleIso (DerivedCategory.quotientCompQhIso C)).app _
  · rintro ⟨X, Y, f, ⟨e⟩⟩
    refine isomorphic_distinguished _ (DerivedCategory.Qh.map_distinguished _ ?_) _
      (e ≪≫ (Functor.mapTriangleIso (DerivedCategory.quotientCompQhIso C)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) DerivedCategory.Qh).app _)
    exact ⟨_, _, f, ⟨Iso.refl _⟩⟩

end

section

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

theorem singleFunctorsPostcompQIso_hom_hom (n : ℤ) :
    (DerivedCategory.singleFunctorsPostcompQIso C).hom.hom n = 𝟙 _ := by
  ext X
  dsimp [DerivedCategory.singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp]
  rfl

end

section

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

set_option backward.isDefEq.respectTransparency false in
theorem singleFunctorsPostcompQIso_inv_hom (n : ℤ) :
    (DerivedCategory.singleFunctorsPostcompQIso C).inv.hom n = 𝟙 _ := by
  ext X
  simp [DerivedCategory.singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso]
  rfl

end
