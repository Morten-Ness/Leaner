import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S T M : Type*}

variable [Semiring k] [AddMonoid G] [Semiring R] [Semiring S] [Semiring T] [AddMonoid M]

theorem liftNCRingHom_single (f : k →+* R) (g : Multiplicative G →* R) (h_comm) (a : G) (b : k) :
    AddMonoidAlgebra.liftNCRingHom f g h_comm (single a b) = f b * g (.ofAdd a) := AddMonoidAlgebra.liftNC_single _ _ _ _

