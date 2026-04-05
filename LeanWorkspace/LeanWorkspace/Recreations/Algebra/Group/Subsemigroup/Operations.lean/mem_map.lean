import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem mem_map {f : M →ₙ* N} {S : Subsemigroup M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y := mem_image _ _ _

