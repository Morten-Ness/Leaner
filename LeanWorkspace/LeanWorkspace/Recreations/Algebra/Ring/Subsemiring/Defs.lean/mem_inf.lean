import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem mem_inf {p p' : Subsemiring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := Iff.rfl

