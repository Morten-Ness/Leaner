import Mathlib

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {h e f : L}

theorem f_ne_zero (t : IsSl2Triple h e f) : f ≠ 0 := by
  have := t.h_ne_zero
  contrapose! this
  simpa [this] using IsSl2Triple.symm t.lie_e_f

