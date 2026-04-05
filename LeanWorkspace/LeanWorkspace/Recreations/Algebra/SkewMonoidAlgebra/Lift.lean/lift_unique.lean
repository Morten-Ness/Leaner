import Mathlib

variable {k G H : Type*}

variable [CommSemiring k] [Monoid G] [Monoid H]

variable {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

variable [MulSemiringAction G k] [SMulCommClass G k k]

theorem lift_unique (F : AlgHom k (SkewMonoidAlgebra k G) A)
    (f : SkewMonoidAlgebra k G) : F f = f.sum fun a b ↦ b • F (single a 1) := by
  conv_lhs =>
    rw [SkewMonoidAlgebra.lift_unique' F]
    simp [SkewMonoidAlgebra.lift_apply]

