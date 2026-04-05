import Mathlib

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {h e f : L}

variable {m : M} {μ : R}

theorem lie_e_pow_toEnd_e (n : ℕ) :
    ⁅e, φ n⁆ = φ (n + 1) := by
  simp [pow_succ']

