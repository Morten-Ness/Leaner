import Mathlib

theorem mul_of {A : Type*} [Monoid A] (a b : A) :
    @HMul.hMul (MonCat.of A) (MonCat.of A) (MonCat.of A) _ a b = a * b := rfl

