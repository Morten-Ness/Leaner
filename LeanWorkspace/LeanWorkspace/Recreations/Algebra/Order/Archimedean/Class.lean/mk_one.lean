import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_one : MulArchimedeanClass.mk 1 = (⊤ : MulArchimedeanClass M) := rfl

