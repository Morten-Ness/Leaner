import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem le_ker_iff : I ≤ f.ker ↔ ∀ x, x ∈ I → f x = 0 := by
  constructor <;> intro h x hx
  · specialize h hx; rw [LieHom.mem_ker] at h; exact h
  · rw [LieHom.mem_ker]; apply h x hx

