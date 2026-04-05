import Mathlib

variable {m n R A : Type*} [CommRing R] [Fintype m] [Fintype n] [CommRing A] [IsDomain A]
  {M : Matrix m n R}

theorem nondegenerate_def : M.Nondegenerate ↔
   (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0) ∧ (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0) := by
  constructor
  · exact fun h ↦ ⟨Matrix.separatingLeft_def.mp h.1, Matrix.separatingRight_def.mp h.2⟩
  · exact fun h ↦ ⟨Matrix.separatingLeft_def.mpr h.1, Matrix.separatingRight_def.mpr h.2⟩

