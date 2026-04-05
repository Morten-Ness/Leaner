import Mathlib

variable {R : Type u} [CommRing R]

theorem braiding_hom_apply {M N : ModuleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).hom : M ⊗ N ⟶ N ⊗ M) (m ⊗ₜ n) = n ⊗ₜ m := rfl

