import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S T M : Type*}

variable [NonAssocSemiring R] [Semiring k] [One G]

theorem liftNC_one {g_hom : Type*} [FunLike g_hom G R] [OneHomClass g_hom G R]
    (f : k →+* R) (g : g_hom) :
    MonoidAlgebra.liftNC (f : k →+ R) g 1 = 1 := by simp [one_def]

