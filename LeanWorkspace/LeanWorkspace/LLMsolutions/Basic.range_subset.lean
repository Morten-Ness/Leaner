import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem range_subset : Set.range (algebraMap R A) ⊆ S := by
  rintro _ ⟨r, rfl⟩
  exact S.algebraMap_mem r
