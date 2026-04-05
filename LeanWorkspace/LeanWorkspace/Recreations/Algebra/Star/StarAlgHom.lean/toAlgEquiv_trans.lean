import Mathlib

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [Star A] [Star B]

theorem toAlgEquiv_trans {C : Type*} [Semiring C] [Algebra R C] [Star C] (f : A ≃⋆ₐ[R] B)
    (g : B ≃⋆ₐ[R] C) : (f.trans g).toAlgEquiv = f.toAlgEquiv.trans g.toAlgEquiv := rfl

