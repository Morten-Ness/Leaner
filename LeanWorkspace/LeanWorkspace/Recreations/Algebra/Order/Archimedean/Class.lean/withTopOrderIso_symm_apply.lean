import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem withTopOrderIso_symm_apply {a : M} (h : a ≠ 1) :
    (FiniteMulArchimedeanClass.withTopOrderIso M).symm (MulArchimedeanClass.mk a) = FiniteMulArchimedeanClass.mk a h := WithTop.subtypeOrderIso_symm_apply (MulArchimedeanClass.mk_eq_top_iff.ne.mpr h)

