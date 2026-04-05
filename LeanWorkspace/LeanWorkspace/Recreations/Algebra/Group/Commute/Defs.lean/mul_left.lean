import Mathlib

variable {G M S : Type*}

variable [Semigroup S] {a b c : S}

theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c := SemiconjBy.mul_left hac hbc

