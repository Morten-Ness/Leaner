import Mathlib

variable {α : Type u} {R : Type v}

theorem right_distrib [Mul R] [Add R] [RightDistribClass R] (a b c : R) :
    (a + b) * c = a * c + b * c := RightDistribClass.right_distrib a b c

alias add_mul := right_distrib

