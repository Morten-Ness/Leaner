import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (φ₃ : K₃ ⟶ L₃)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)

variable (comm : φ₁ ≫ b = a ≫ φ₂)

variable (a' : K₂ ⟶ K₃) (b' : L₂ ⟶ L₃)

theorem map_comp (comm' : φ₂ ≫ b' = a' ≫ φ₃) :
    CochainComplex.mappingCone.map φ₁ φ₃ (a ≫ a') (b ≫ b') (by rw [reassoc_of% comm, comm', assoc]) =
      CochainComplex.mappingCone.map φ₁ φ₂ a b comm ≫ CochainComplex.mappingCone.map φ₂ φ₃ a' b' comm' := by
  ext n
  simp [ext_from_iff _ (n + 1) n rfl, CochainComplex.mappingCone.map]

