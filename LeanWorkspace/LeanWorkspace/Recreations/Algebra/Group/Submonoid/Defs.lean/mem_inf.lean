import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable {S : Submonoid M}

theorem mem_inf {p p' : Submonoid M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := Iff.rfl

