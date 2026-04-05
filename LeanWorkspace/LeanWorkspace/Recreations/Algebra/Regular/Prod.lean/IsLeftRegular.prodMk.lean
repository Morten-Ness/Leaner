import Mathlib

variable {α R S : Type*}

variable [Mul R] [Mul S]

theorem IsLeftRegular.prodMk {a : R} {b : S} (ha : IsLeftRegular a) (hb : IsLeftRegular b) :
    IsLeftRegular (a, b) := Prod.isLeftRegular_mk.2 ⟨ha, hb⟩

