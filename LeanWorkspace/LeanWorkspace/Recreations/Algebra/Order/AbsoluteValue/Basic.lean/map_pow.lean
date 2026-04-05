import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

variable [IsDomain S] [Nontrivial R]

theorem map_pow (a : R) (n : ℕ) : abv (a ^ n) = abv a ^ n := abv.toMonoidHom.map_pow a n

