import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (φ : A →ₐ[R] B)

theorem range_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range = f.range.map g := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨f a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
