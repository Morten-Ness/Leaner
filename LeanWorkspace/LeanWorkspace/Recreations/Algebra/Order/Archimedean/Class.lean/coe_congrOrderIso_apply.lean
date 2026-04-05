import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

theorem coe_congrOrderIso_apply (e : MulArchimedeanClass M ≃o MulArchimedeanClass N)
    (a : FiniteMulArchimedeanClass M) :
    (FiniteMulArchimedeanClass.congrOrderIso e a : MulArchimedeanClass N) = e a := rfl

