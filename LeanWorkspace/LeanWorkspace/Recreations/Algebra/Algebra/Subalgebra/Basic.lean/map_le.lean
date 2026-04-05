import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem map_le {S : Subalgebra R A} {f : A →ₐ[R] B} {U : Subalgebra R B} :
    Subalgebra.map f S ≤ U ↔ S ≤ Subalgebra.comap f U := Set.image_subset_iff

