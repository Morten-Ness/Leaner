import Mathlib

variable {M N α β : Type*}

variable [AddMonoid M] [AddCommMonoid N]

theorem AddMonoidHom.toMultiplicative_add (f g : M →+ N) :
    (f + g).toMultiplicative = f.toMultiplicative * g.toMultiplicative := rfl

