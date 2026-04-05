import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

omit [IsDomain R] in
theorem Splits.aeval_eq_prod_aroots [IsSimpleRing R]
    (hf : (f.map (algebraMap R A)).Splits) (x : A) :
    f.aeval x = algebraMap R A f.leadingCoeff * ((f.aroots A).map (x - ·)).prod := by
  simp [← eval_map_algebraMap, hf.eval_eq_prod_roots]

