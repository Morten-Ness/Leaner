import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem splits_iff_card_roots : Polynomial.Splits f ↔ f.roots.card = f.natDegree := ⟨fun h ↦ h.natDegree_eq_card_roots.symm, fun h ↦ Polynomial.splits_iff_exists_multiset.mpr
    ⟨f.roots, (C_leadingCoeff_mul_prod_multiset_X_sub_C h).symm⟩⟩

