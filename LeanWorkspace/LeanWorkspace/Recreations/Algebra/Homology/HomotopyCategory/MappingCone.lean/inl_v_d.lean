import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem inl_v_d (i j k : ℤ) (hij : i + (-1) = j) (hik : k + (-1) = i) :
    (CochainComplex.mappingCone.inl φ).v i j hij ≫ (CochainComplex.mappingCone φ).d j i =
      φ.f i ≫ (CochainComplex.mappingCone.inr φ).f i - F.d i k ≫ (CochainComplex.mappingCone.inl φ).v _ _ hik := by
  dsimp [CochainComplex.mappingCone, CochainComplex.mappingCone.inl, CochainComplex.mappingCone.inr]
  rw [homotopyCofiber.inlX_d φ j i k (by dsimp; lia) (by dsimp; lia)]
  abel

