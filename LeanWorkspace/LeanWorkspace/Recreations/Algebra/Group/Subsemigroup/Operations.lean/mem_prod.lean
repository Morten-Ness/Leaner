import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem mem_prod {s : Subsemigroup M} {t : Subsemigroup N} {p : M × N} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := Iff.rfl

