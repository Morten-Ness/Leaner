import Mathlib

variable {R : Type u} [CommSemiring R]

theorem leftUnitor_inv_apply {M : SemimoduleCat.{u} R} (m : M) :
    ((λ_ M).inv : M ⟶ 𝟙_ (SemimoduleCat.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m := TensorProduct.lid_symm_apply m

