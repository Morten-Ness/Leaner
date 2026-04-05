import Mathlib

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

