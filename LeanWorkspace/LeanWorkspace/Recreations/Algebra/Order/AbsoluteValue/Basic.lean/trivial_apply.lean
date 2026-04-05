import Mathlib

variable {ι α R S : Type*}

variable {R : Type*} [Semiring R] [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]

variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S] [Nontrivial S]

theorem trivial_apply {x : R} (hx : x ≠ 0) : AbsoluteValue.trivial (S := S) x = 1 :=
  if_neg hx

