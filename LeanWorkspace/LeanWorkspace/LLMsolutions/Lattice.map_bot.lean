import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_bot (f : A →ₐ[R] B) : (⊥ : Subalgebra R A).map f = ⊥ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨r, rfl⟩
    exact ⟨r, by simp⟩
  · rintro ⟨r, rfl⟩
    refine ⟨algebraMap R A r, ?_, by simp⟩
    exact ⟨r, rfl⟩
