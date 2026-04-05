import Mathlib

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {h e f : L}

theorem lie_h_e_smul (t : IsSl2Triple h e f) : ⁅h, e⁆ = (2 : R) • e := by
  simp [t.lie_h_e_nsmul, two_smul]

