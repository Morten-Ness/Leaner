import Mathlib

variable {G M S : Type*}

variable [Semigroup S] {a b c : S}

theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) := SemiconjBy.mul_right hab hac

