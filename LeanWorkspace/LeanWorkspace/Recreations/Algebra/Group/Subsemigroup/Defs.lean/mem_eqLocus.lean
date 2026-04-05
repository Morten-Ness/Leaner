import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable [Mul N]

theorem mem_eqLocus {f g : M →ₙ* N} {x : M} : x ∈ f.eqLocus g ↔ f x = g x := Iff.rfl

