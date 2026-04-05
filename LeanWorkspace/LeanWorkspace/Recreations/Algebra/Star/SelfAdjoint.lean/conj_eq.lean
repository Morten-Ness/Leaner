import Mathlib

open scoped ComplexConjugate

variable {R A : Type*}

variable {α : Type*} [CommSemiring α] [StarRing α] {a : α}

theorem conj_eq (ha : IsSelfAdjoint a) : conj a = a := IsSelfAdjoint.star_eq ha

