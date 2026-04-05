import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_out (A : MulArchimedeanClass M) : MulArchimedeanClass.mk A.out = A := Quotient.out_eq' A

