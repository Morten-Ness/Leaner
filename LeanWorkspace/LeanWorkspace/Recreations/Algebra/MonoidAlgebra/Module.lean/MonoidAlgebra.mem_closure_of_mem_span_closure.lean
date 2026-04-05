import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable [Semiring R] [Semiring S] [MulOneClass M] {s : Set M} {m : M}

theorem mem_closure_of_mem_span_closure [Nontrivial R]
    (h : of R M m ∈ Submodule.span R (Submonoid.closure <| of R M '' s)) :
    m ∈ Submonoid.closure s := by
  rw [← MonoidHom.map_mclosure] at h; simpa using MonoidAlgebra.of_mem_span_of_iff.1 h

