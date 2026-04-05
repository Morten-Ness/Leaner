import Mathlib

variable {R : Type u} [CommSemiring R]

theorem braiding_hom_apply {M N : SemimoduleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).hom : M ⊗ N ⟶ N ⊗ M) (m ⊗ₜ n) = n ⊗ₜ m := rfl

