import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

variable [IsDomain S] [Nontrivial R]

theorem coe_toMonoidWithZeroHom : ⇑abv.toMonoidWithZeroHom = abv := rfl

