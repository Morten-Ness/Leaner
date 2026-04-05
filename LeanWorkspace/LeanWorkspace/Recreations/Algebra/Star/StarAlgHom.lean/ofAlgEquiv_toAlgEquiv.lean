import Mathlib

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [Star A] [Star B]

theorem ofAlgEquiv_toAlgEquiv (f : A ≃⋆ₐ[R] B) (map_star) :
    StarAlgEquiv.ofAlgEquiv f.toAlgEquiv map_star = f := rfl

