import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] (a b : α)

theorem mul_self : a * a = a := IsIdempotentElem.eq (isIdempotentElem a)

