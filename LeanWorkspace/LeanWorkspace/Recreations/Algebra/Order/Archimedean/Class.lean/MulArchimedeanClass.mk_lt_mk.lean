import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_lt_mk : MulArchimedeanClass.mk a < MulArchimedeanClass.mk b ↔ ∀ n, |b|ₘ ^ n < |a|ₘ := .rfl

