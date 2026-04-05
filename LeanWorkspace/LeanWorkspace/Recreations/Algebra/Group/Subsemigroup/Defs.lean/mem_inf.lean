import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable {S : Subsemigroup M}

theorem mem_inf {p p' : Subsemigroup M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := Iff.rfl

