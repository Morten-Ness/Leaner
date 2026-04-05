import Mathlib

variable {k G H : Type*}

variable [CommSemiring k] [Monoid G] [Monoid H]

variable {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

variable [MulSemiringAction G k] [SMulCommClass G k k]

theorem lift_apply (F : G →* A) (f : SkewMonoidAlgebra k G) :
    SkewMonoidAlgebra.lift k G A F f = f.sum fun a b ↦ b • F a := by simp [SkewMonoidAlgebra.lift_apply', Algebra.smul_def]

