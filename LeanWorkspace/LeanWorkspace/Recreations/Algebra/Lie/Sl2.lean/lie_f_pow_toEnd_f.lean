import Mathlib

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {h e f : L}

variable {m : M} {μ : R} {t : IsSl2Triple h e f}

set_option linter.unusedVariables false in
theorem lie_f_pow_toEnd_f (P : IsSl2Triple.HasPrimitiveVectorWith t m μ) (n : ℕ) :
    ⁅f, ψ n⁆ = ψ (n + 1) := by
  simp [pow_succ']

