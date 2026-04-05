import Mathlib

variable {M N A B C : Type*}

variable [Zero A] [Zero B] [Zero C]

theorem smul_comp [SMulZeroClass M C] (m : M) (g : ZeroHom B C) (f : ZeroHom A B) :
    (m • g).comp f = m • g.comp f := rfl

