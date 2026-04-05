import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S T M : Type*}

variable [Semiring k] [Monoid G] [Semiring R] [Semiring S] [Semiring T] [Monoid M]

theorem liftNCRingHom_single (f : k →+* R) (g : G →* R) (h_comm) (a : G) (b : k) :
    MonoidAlgebra.liftNCRingHom f g h_comm (single a b) = f b * g a := MonoidAlgebra.liftNC_single _ _ _ _

