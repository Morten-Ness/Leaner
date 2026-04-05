import Mathlib

variable {R : Type u} [CommRing R]

theorem tensorμ_apply
    {A B C D : ModuleCat R} (x : A) (y : B) (z : C) (w : D) :
    tensorμ A B C D ((x ⊗ₜ y) ⊗ₜ (z ⊗ₜ w)) = (x ⊗ₜ z) ⊗ₜ (y ⊗ₜ w) := rfl

