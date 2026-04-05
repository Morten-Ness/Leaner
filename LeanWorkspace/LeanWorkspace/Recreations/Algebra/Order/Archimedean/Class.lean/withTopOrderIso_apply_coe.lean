import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem withTopOrderIso_apply_coe (A : FiniteMulArchimedeanClass M) :
    FiniteMulArchimedeanClass.withTopOrderIso M (A : WithTop (FiniteMulArchimedeanClass M)) = A.val := WithTop.subtypeOrderIso_apply_coe A

