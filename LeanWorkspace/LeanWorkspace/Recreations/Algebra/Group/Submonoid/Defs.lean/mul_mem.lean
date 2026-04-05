import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable {S : Submonoid M}

theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S := mul_mem

