import Mathlib

variable {α R S : Type*}

variable [Mul R] [Mul S]

theorem IsRegular.prodMk {a : R} {b : S} (ha : IsRegular a) (hb : IsRegular b) :
    IsRegular (a, b) := Prod.isRegular_mk.2 ⟨ha, hb⟩

