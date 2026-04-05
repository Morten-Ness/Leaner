import Mathlib

variable {R : Type u} [CommRing R]

theorem monoidalClosed_uncurry
    {M N P : ModuleCat.{u} R} (f : N ⟶ M ⟶[ModuleCat.{u} R] P) (x : M) (y : N) :
    MonoidalClosed.uncurry f (x ⊗ₜ[R] y) = (f y).hom x := rfl

