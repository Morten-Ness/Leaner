import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable [Semiring R] [Semiring S] [MulOneClass M] {s : Set M} {m : M}

theorem smul_of (m : M) (r : R) : r • of R M m = single m r := by simp

