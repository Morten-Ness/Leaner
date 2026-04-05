import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_le_mk : MulArchimedeanClass.mk a ≤ MulArchimedeanClass.mk b ↔ ∃ n, |b|ₘ ≤ |a|ₘ ^ n := .rfl

