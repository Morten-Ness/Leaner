import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

theorem distinguished_cocone_triangle {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    ∃ (Z : HomotopyCategory C (ComplexShape.up ℤ)) (g : Y ⟶ Z) (h : Z ⟶ X⟦1⟧),
      Triangle.mk f g h ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C := by
  obtain ⟨f, rfl⟩ := (quotient _ _).map_surjective f
  exact ⟨_, _, _, ⟨_, _, f, ⟨Iso.refl _⟩⟩⟩

