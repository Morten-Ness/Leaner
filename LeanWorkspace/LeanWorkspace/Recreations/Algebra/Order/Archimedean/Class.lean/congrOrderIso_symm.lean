import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

theorem congrOrderIso_symm (e : MulArchimedeanClass M ≃o MulArchimedeanClass N) :
    (FiniteMulArchimedeanClass.congrOrderIso e).symm = FiniteMulArchimedeanClass.congrOrderIso e.symm := rfl

