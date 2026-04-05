import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_comap (S : Subsemigroup P) (g : N →ₙ* P) (f : M →ₙ* N) :
    (S.comap g).comap f = S.comap (g.comp f) := rfl

