import Mathlib

variable {k G H : Type*}

variable [CommSemiring k] [Monoid G] [Monoid H]

variable {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

variable [MulSemiringAction G k] [SMulCommClass G k k]

theorem lift_single (F : G →* A) (a b) : SkewMonoidAlgebra.lift k G A F (single a b) = b • F a := by
  rw [SkewMonoidAlgebra.lift_def, liftNC_single, Algebra.smul_def, AddMonoidHom.coe_coe]

