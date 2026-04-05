import Mathlib

variable {R : Type u} {S : Type u₁}

variable {F R : Type*} [CommSemiring R]

variable {A B : Type*} [Semiring A] [Semiring B] [Algebra R A]
  [Algebra R B]

theorem toNonUnitalAlgHom_eq_coe (f : A →ₐ[R] B) : f.toNonUnitalAlgHom = f := rfl

