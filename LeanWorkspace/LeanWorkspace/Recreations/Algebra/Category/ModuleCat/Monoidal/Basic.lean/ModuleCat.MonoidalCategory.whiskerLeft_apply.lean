import Mathlib

variable {R : Type u} [CommRing R]

theorem whiskerLeft_apply (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (l : L) (m : M) :
    (L ◁ f) (l ⊗ₜ m) = l ⊗ₜ f m := rfl

