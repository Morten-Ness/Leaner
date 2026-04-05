import Mathlib

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {h e f : L}

theorem symm (ht : IsSl2Triple h e f) : IsSl2Triple (-h) f e where
  h_ne_zero := by simpa using ht.h_ne_zero
  lie_e_f := by rw [← neg_eq_iff_eq_neg, lie_skew, ht.lie_e_f]
  lie_h_e_nsmul := by rw [neg_lie, neg_eq_iff_eq_neg, ht.lie_h_f_nsmul]
  lie_h_f_nsmul := by rw [neg_lie, neg_inj, ht.lie_h_e_nsmul]

