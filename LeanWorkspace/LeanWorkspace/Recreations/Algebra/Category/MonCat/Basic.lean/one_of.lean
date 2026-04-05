import Mathlib

theorem one_of {A : Type*} [Monoid A] : (1 : MonCat.of A) = (1 : A) := rfl

