import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S T M : Type*}

variable [Semiring k] [Add G] [Semiring R]

theorem liftNC_mul {g_hom : Type*}
    [FunLike g_hom (Multiplicative G) R] [MulHomClass g_hom (Multiplicative G) R]
    (f : k →+* R) (g : g_hom) (a b : k[G])
    (h_comm : ∀ {x y}, y ∈ a.support → Commute (f (b x)) (g <| Multiplicative.ofAdd y)) :
    AddMonoidAlgebra.liftNC (f : k →+ R) g (a * b) = AddMonoidAlgebra.liftNC (f : k →+ R) g a * AddMonoidAlgebra.liftNC (f : k →+ R) g b := MonoidAlgebra.liftNC_mul f g _ _ @h_comm

