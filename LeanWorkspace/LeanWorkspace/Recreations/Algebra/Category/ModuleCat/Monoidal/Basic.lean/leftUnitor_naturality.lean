import Mathlib

variable {R : Type u} [CommSemiring R]

theorem leftUnitor_naturality {M N : SemimoduleCat R} (f : M ⟶ N) :
    SemimoduleCat.MonoidalCategory.tensorHom (𝟙 (SemimoduleCat.of R R)) f ≫ (SemimoduleCat.MonoidalCategory.leftUnitor N).hom = (SemimoduleCat.MonoidalCategory.leftUnitor M).hom ≫ f := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [SemimoduleCat.MonoidalCategory.tensorHom, SemimoduleCat.MonoidalCategory.tensorObj, SemimoduleCat.MonoidalCategory.leftUnitor]

