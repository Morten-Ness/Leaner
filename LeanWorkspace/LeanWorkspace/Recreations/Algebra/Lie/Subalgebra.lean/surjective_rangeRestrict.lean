import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

theorem surjective_rangeRestrict : Function.Surjective f.rangeRestrict := by
  rintro ⟨y, hy⟩
  rw [LieHom.mem_range] at hy; obtain ⟨x, rfl⟩ := hy
  use x
  simp only [LieHom.rangeRestrict_apply]

