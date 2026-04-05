import Mathlib

variable {R : Type u} [CommSemiring R]

theorem rightUnitor_hom_apply {M : SemimoduleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).hom : M ⊗ 𝟙_ (SemimoduleCat R) ⟶ M) (m ⊗ₜ r) = r • m := TensorProduct.rid_tmul m r

