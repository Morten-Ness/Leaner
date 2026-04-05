import Mathlib

variable {G : Type*}

variable [Semigroup G] {a b c : G}

theorem Commute.function_commute_mul_left (h : Commute a b) : Function.Commute (a * ·) (b * ·) := SemiconjBy.function_semiconj_mul_left h

