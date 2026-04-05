import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable {S : Subsemigroup M}

theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S := Subsemigroup.mul_mem' S

