import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem gc_map_comap (f : A →ₐ[R] B) : GaloisConnection (Subalgebra.map f) (Subalgebra.comap f) := fun _S _U => Subalgebra.map_le

