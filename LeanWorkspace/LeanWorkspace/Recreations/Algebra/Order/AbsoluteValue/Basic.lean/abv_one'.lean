import Mathlib

variable {ι α R S : Type*}

variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S] [IsCancelMulZero S]

variable {R : Type*} [Semiring R] [Nontrivial R] (abv : R → S) [IsAbsoluteValue abv]

omit [IsOrderedRing S] in
theorem abv_one' : abv 1 = 1 := AbsoluteValue.map_one_of_isLeftRegular (IsAbsoluteValue.toAbsoluteValue abv) <|
    (IsRegular.of_ne_zero <| (IsAbsoluteValue.toAbsoluteValue abv).ne_zero one_ne_zero).left

