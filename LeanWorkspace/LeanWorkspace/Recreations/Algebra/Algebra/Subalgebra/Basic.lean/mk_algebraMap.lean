import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem mk_algebraMap {S : Subalgebra R A} (r : R) (hr : algebraMap R A r ∈ S) :
    ⟨algebraMap R A r, hr⟩ = algebraMap R S r := rfl

