import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem rangeS_le : (algebraMap R A).rangeS ≤ S.toSubsemiring := by
  intro x hx
  rcases hx with ⟨r, rfl⟩
  exact S.algebraMap_mem r
