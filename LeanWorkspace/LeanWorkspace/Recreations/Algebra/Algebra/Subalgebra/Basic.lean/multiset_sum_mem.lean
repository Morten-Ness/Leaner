import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem multiset_sum_mem {m : Multiset A} (h : ∀ x ∈ m, x ∈ S) : m.sum ∈ S := multiset_sum_mem m h

