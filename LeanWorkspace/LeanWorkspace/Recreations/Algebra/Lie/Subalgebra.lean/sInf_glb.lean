import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

theorem sInf_glb (S : Set (LieSubalgebra R L)) : IsGLB S (sInf S) := by
  have h : ∀ K K' : LieSubalgebra R L, (K : Set L) ≤ K' ↔ K ≤ K' := by
    intros
    exact Iff.rfl
  apply IsGLB.of_image @h
  simp only [LieSubalgebra.coe_sInf]
  exact isGLB_biInf

