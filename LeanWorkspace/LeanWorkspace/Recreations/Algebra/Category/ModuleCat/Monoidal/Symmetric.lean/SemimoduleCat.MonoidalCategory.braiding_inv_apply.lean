import Mathlib

variable {R : Type u} [CommSemiring R]

theorem braiding_inv_apply {M N : SemimoduleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).inv : N ⊗ M ⟶ M ⊗ N) (n ⊗ₜ m) = m ⊗ₜ n := rfl

