import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

variable (f : A →ₐ[R] B)

theorem range_comp_val : (f.comp S.val).range = S.map f := by
  rw [AlgHom.range_comp, Subalgebra.range_val]

