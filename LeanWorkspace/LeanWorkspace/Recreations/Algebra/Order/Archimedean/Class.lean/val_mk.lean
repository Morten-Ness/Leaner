import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem val_mk {a : M} (h : a ≠ 1) : (FiniteMulArchimedeanClass.mk a h).val = MulArchimedeanClass.mk a := rfl

