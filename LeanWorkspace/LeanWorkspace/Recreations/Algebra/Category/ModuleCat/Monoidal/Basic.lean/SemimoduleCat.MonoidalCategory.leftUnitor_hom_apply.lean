import Mathlib

variable {R : Type u} [CommSemiring R]

theorem leftUnitor_hom_apply {M : SemimoduleCat.{u} R} (r : R) (m : M) :
    ((λ_ M).hom : 𝟙_ (SemimoduleCat R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m := TensorProduct.lid_tmul m r

