import Mathlib

variable {M : Type*}

variable [Mul M] {s t : Set M} {x : M}

theorem mul_mem (I : SemigroupIdeal M) (x : M) {y : M} : y ∈ I → x * y ∈ I := SubMulAction.smul_mem I x

