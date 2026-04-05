import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (h : K ≤ K')

theorem mem_ofLe (x : K') : x ∈ LieSubalgebra.ofLe h ↔ (x : L) ∈ K := by
  simp only [LieSubalgebra.ofLe, LieSubalgebra.inclusion_apply, LieHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro h
    use ⟨(x : L), h⟩

