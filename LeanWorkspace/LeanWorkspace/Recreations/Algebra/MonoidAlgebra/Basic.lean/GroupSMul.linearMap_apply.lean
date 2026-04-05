import Mathlib

variable {R S T A B C M N O : Type*}

theorem GroupSMul.linearMap_apply [Monoid M] [CommSemiring R] (V : Type*) [AddCommMonoid V]
    [Module R V] [Module R[M] V] [IsScalarTower R R[M] V] (g : M) (v : V) :
    (MonoidAlgebra.GroupSMul.linearMap R V g) v = single g (1 : R) • v := rfl

