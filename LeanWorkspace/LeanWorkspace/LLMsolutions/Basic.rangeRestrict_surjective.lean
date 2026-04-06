import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (φ : A →ₐ[R] B)

theorem rangeRestrict_surjective (f : A →ₐ[R] B) : Function.Surjective (f.rangeRestrict) := by
  intro y
  rcases y with ⟨b, hb⟩
  rcases hb with ⟨a, rfl⟩
  refine ⟨a, ?_⟩
  rfl
