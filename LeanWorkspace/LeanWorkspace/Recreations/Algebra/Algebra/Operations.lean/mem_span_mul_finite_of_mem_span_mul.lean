import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mem_span_mul_finite_of_mem_span_mul {R A} [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] {S : Set A} {S' : Set A} {x : A} (hx : x ∈ span R (S * S')) :
    ∃ T T' : Finset A, ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ x ∈ span R (T * T' : Set A) := by
  classical
  obtain ⟨U, h, hU⟩ := mem_span_finite_of_mem_span hx
  obtain ⟨T, T', hS, hS', h⟩ := Finset.subset_mul h
  use T, T', hS, hS'
  have h' : (U : Set A) ⊆ T * T' := by assumption_mod_cast
  have h'' := span_mono h' hU
  assumption

