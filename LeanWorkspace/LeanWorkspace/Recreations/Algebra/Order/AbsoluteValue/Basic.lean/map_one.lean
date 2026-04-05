import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

variable [IsDomain S] [Nontrivial R]

theorem map_one : abv 1 = 1 := AbsoluteValue.map_one_of_isLeftRegular abv (IsRegular.of_ne_zero <| abv.ne_zero one_ne_zero).left

