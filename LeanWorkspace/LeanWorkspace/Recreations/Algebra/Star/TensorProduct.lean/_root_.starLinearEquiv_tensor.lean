import Mathlib

open scoped TensorProduct

variable {R A B : Type*}
  [CommSemiring R] [StarRing R]
  [AddCommMonoid A] [StarAddMonoid A] [Module R A] [StarModule R A]
  [AddCommMonoid B] [StarAddMonoid B] [Module R B] [StarModule R B]

theorem _root_.starLinearEquiv_tensor :
    starLinearEquiv R (A := A ⊗[R] B) = congr (starLinearEquiv R) (starLinearEquiv R) := rfl

