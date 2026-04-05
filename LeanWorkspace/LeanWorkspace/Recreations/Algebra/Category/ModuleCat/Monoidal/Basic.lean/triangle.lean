import Mathlib

variable {R : Type u} [CommSemiring R]

theorem triangle (M N : SemimoduleCat.{u} R) :
    (SemimoduleCat.MonoidalCategory.associator M (SemimoduleCat.of R R) N).hom ≫ SemimoduleCat.MonoidalCategory.tensorHom (𝟙 M) (SemimoduleCat.MonoidalCategory.leftUnitor N).hom =
      SemimoduleCat.MonoidalCategory.tensorHom (SemimoduleCat.MonoidalCategory.rightUnitor M).hom (𝟙 N) := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y
  exact TensorProduct.tmul_smul _ _

