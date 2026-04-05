import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

omit [IsDomain R] in
theorem Splits.aeval_eq_prod_aroots_of_monic
    (hf : (f.map (algebraMap R A)).Splits) (hm : Monic f) (x : A) :
    f.aeval x = ((f.aroots A).map (x - ·)).prod := by
  simp [hf.eval_eq_prod_roots_of_monic (hm.map (algebraMap R A)), ← eval_map_algebraMap]

