import Mathlib

variable {ι α R S : Type*}

variable {R : Type*} [Semiring R] {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]

omit [IsOrderedRing S] in
theorem not_isNontrivial_apply {v : AbsoluteValue R S} (hv : ¬ v.IsNontrivial) {x : R} (hx : x ≠ 0) :
    v x = 1 := AbsoluteValue.not_isNontrivial_iff v.mp hv _ hx

