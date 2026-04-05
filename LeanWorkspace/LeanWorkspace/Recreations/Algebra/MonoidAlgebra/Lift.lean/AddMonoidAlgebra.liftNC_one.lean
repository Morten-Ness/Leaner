import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S T M : Type*}

variable [Semiring k] [Zero G] [NonAssocSemiring R]

theorem liftNC_one {g_hom : Type*}
    [FunLike g_hom (Multiplicative G) R] [OneHomClass g_hom (Multiplicative G) R]
    (f : k →+* R) (g : g_hom) : AddMonoidAlgebra.liftNC (f : k →+ R) g 1 = 1 := MonoidAlgebra.liftNC_one f g

