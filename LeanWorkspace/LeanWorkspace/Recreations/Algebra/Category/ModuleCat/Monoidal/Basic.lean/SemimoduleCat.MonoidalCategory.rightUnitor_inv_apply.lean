import Mathlib

variable {R : Type u} [CommSemiring R]

theorem rightUnitor_inv_apply {M : SemimoduleCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (SemimoduleCat.{u} R)) m = m ⊗ₜ[R] 1 := TensorProduct.rid_symm_apply m

