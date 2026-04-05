import Mathlib

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [Star A] [Star B]

theorem ofAlgEquiv_apply (f : A ≃ₐ[R] B) (map_star : ∀ x, f (star x) = star (f x)) (x : A) :
    StarAlgEquiv.ofAlgEquiv f map_star x = f x := rfl

