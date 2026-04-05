import Mathlib

variable {G M S : Type*}

theorem commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b = b * a := Iff.rfl

