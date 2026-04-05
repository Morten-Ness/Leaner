import Mathlib

variable {M N S : Type*}

variable [CommSemigroup S] {a b : S}

theorem mul (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem (a * b) := IsIdempotentElem.mul_of_commute ha (.all ..) hb

