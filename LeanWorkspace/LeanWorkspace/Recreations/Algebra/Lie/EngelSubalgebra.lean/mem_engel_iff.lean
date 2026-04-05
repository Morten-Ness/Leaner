import Mathlib

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem mem_engel_iff (x y : L) :
    y ∈ LieSubalgebra.engel R x ↔ ∃ n : ℕ, ((ad R L x) ^ n) y = 0 := (Module.End.mem_maxGenEigenspace _ _ _).trans <| by simp only [zero_smul, sub_zero]

