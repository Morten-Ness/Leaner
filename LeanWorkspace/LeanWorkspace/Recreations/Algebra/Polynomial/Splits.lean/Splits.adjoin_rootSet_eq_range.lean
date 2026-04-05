import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

omit [IsDomain R] in
theorem Splits.adjoin_rootSet_eq_range [IsSimpleRing A]
    (hf : (f.map (algebraMap R A)).Splits) (g : A →ₐ[R] B) :
    Algebra.adjoin R (f.rootSet B) = g.range ↔ Algebra.adjoin R (f.rootSet A) = ⊤ := by
  rw [← hf.image_rootSet g, Algebra.adjoin_image, ← Algebra.map_top]
  exact (Subalgebra.map_injective g.injective).eq_iff

