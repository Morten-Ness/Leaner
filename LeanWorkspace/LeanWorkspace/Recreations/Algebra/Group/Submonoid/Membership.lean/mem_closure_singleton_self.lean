import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem mem_closure_singleton_self {y : M} : y ∈ closure ({y} : Set M) := Submonoid.mem_closure_singleton.2 ⟨1, pow_one y⟩

