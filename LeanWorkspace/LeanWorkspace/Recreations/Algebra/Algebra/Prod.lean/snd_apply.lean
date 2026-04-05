import Mathlib

variable {R A B C : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem snd_apply (a) : AlgHom.snd R A B a = a.2 := rfl

