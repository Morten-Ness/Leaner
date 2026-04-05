import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem isZero_X_iff (i : ℤ) :
    IsZero ((CochainComplex.mappingCone φ).X i) ↔ IsZero (F.X (i + 1)) ∧ IsZero (G.X i) := by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ i (i + 1) rfl
  rw [← biprod_isZero_iff]
  exact (homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).isZero_iff

