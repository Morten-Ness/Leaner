import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R]

theorem of'_commute [AddZeroClass M] {a : M} (h : ∀ a', AddCommute a a') (f : AddMonoidAlgebra R M) :
    Commute (AddMonoidAlgebra.of' R M a) f := MonoidAlgebra.single_commute h .one_left f

