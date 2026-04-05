import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

theorem Splits.comp_X_sub_C (hf : f.Splits) (a : R) : (f.comp (X - C a)).Splits := hf.comp_of_natDegree_le_one_of_monic (natDegree_sub_C.trans_le natDegree_X_le) (monic_X_sub_C a)

