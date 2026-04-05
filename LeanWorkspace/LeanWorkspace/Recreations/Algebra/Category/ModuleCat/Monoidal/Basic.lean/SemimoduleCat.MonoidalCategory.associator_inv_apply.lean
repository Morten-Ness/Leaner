import Mathlib

variable {R : Type u} [CommSemiring R]

theorem associator_inv_apply {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M ⊗ N ⊗ K ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = m ⊗ₜ n ⊗ₜ k := rfl

