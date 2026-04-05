import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_lt_mk {a : M} (ha : a ≠ 1) {b : M} (hb : b ≠ 1) :
    FiniteMulArchimedeanClass.mk a ha < FiniteMulArchimedeanClass.mk b hb ↔ MulArchimedeanClass.mk a < MulArchimedeanClass.mk b := .rfl

