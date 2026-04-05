import Mathlib

variable {α R S : Type*}

variable [Mul R] [Mul S]

theorem IsRightRegular.prodMk {a : R} {b : S} (ha : IsRightRegular a) (hb : IsRightRegular b) :
    IsRightRegular (a, b) := Prod.isRightRegular_mk.2 ⟨ha, hb⟩

