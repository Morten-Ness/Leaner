import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem Associates.mk_normalize (x : α) : Associates.mk (normalize x) = Associates.mk x := Associates.mk_eq_mk_iff_associated.2 (normalize_associated _)

