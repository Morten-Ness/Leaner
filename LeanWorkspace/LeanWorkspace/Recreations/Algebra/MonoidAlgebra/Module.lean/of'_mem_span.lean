import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable [Semiring R] [Semiring S]

theorem of'_mem_span [Nontrivial R] {m : M} {s : Set M} :
    of' R M m ∈ Submodule.span R (of' R M '' s) ↔ m ∈ s := single_mem_span_single _

