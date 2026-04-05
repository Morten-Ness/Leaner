import Mathlib

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addEquiv_refl : Finsupp.mapRange.addEquiv (.refl M) = .refl (ι →₀ M) := by ext; simp

