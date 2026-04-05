import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem prod_mem {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) {ι : Type w} {t : Finset ι} {f : ι → A} (h : ∀ x ∈ t, f x ∈ S) :
    (∏ x ∈ t, f x) ∈ S := prod_mem h

