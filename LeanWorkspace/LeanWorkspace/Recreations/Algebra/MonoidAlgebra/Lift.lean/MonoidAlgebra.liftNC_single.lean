import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S T M : Type*}

variable [Semiring k] [NonUnitalNonAssocSemiring R]

theorem liftNC_single (f : k →+ R) (g : G → R) (a : G) (b : k) :
    MonoidAlgebra.liftNC f g (single a b) = f b * g a := liftAddHom_apply_single _ _ _

