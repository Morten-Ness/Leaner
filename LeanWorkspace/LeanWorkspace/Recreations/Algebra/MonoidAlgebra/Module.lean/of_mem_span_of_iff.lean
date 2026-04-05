import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable [Semiring R] [Semiring S] [MulOneClass M] {s : Set M} {m : M}

theorem of_mem_span_of_iff [Nontrivial R] : of R M m ∈ Submodule.span R (of R M '' s) ↔ m ∈ s := single_mem_span_single _

