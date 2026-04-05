import Mathlib

variable {k G H : Type*}

variable [CommSemiring k] [Monoid G] [Monoid H]

variable {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

variable [MulSemiringAction G k] [SMulCommClass G k k]

theorem lift_of (F : G →* A) (x) : SkewMonoidAlgebra.lift k G A F (of k G x) = F x := by
  rw [of_apply, ← SkewMonoidAlgebra.lift_symm_apply, Equiv.symm_apply_apply]

