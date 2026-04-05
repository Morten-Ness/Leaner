import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem mem_srange {f : M →ₙ* N} {y : N} : y ∈ f.srange ↔ ∃ x, f x = y := Iff.rfl

