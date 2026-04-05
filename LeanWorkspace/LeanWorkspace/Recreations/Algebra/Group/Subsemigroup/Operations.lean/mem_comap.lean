import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem mem_comap {S : Subsemigroup N} {f : M →ₙ* N} {x : M} : x ∈ S.comap f ↔ f x ∈ S := Iff.rfl

