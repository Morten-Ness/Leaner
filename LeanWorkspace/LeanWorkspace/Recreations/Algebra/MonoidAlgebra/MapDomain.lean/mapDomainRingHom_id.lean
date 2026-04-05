import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem mapDomainRingHom_id : MonoidAlgebra.mapDomainRingHom R (.id M) = .id R[M] := by ext <;> simp

