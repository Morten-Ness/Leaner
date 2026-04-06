import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R A).map f = f.range := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by trivial, rfl⟩
