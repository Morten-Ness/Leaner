import Mathlib

variable {R : Type u} [CommSemiring R]

theorem whiskerLeft_apply (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f : M ⟶ N)
    (l : L) (m : M) :
    (L ◁ f) (l ⊗ₜ m) = l ⊗ₜ f m := rfl

