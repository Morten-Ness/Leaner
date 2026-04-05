import Mathlib

variable {M N A B C : Type*}

variable [AddZeroClass A] [AddZeroClass B] [AddZeroClass C]

theorem smul_comp [DistribSMul M C] (m : M) (g : B →+ C) (f : A →+ B) :
    (m • g).comp f = m • g.comp f := rfl

