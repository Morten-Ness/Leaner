import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ} {n m : ℤ}

variable (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n)

theorem inl_descCochain :
    (CochainComplex.mappingCone.inl φ).comp (CochainComplex.mappingCone.descCochain φ α β h) (by lia) = α := by
  simp [CochainComplex.mappingCone.descCochain]

