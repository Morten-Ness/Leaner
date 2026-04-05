import Mathlib

variable {R : Type*}

variable [CommSemiring R]

theorem Splits.comp_X_add_C {f : R[X]} (hf : f.Splits) (a : R) : (f.comp (X + C a)).Splits := hf.comp_of_natDegree_le_one_of_monic (natDegree_add_C.trans_le natDegree_X_le) (monic_X_add_C a)

