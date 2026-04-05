import Mathlib

variable {R : Type u} [CommRing R]

theorem monoidalClosed_curry {M N P : ModuleCat.{u} R} (f : M ⊗ N ⟶ P) (x : M) (y : N) :
    ((MonoidalClosed.curry f).hom y).hom x = f (x ⊗ₜ[R] y) := rfl

