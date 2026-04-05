import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_eq : Subsemigroup.closure (S : Set M) = S := (Subsemigroup.gi M).l_u_eq S

