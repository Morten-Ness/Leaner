import Mathlib

variable {α : Type u} {R : Type v}

theorem left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c : R) :
    a * (b + c) = a * b + a * c := LeftDistribClass.left_distrib a b c

alias mul_add := left_distrib

