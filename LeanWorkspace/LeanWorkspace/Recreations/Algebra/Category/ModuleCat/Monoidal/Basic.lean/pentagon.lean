import Mathlib

variable {R : Type u} [CommSemiring R]

theorem pentagon (W X Y Z : SemimoduleCat R) :
    SemimoduleCat.MonoidalCategory.whiskerRight (SemimoduleCat.MonoidalCategory.associator W X Y).hom Z ≫
        (SemimoduleCat.MonoidalCategory.associator W (SemimoduleCat.MonoidalCategory.tensorObj X Y) Z).hom ≫ SemimoduleCat.MonoidalCategory.whiskerLeft W (SemimoduleCat.MonoidalCategory.associator X Y Z).hom =
      (SemimoduleCat.MonoidalCategory.associator (SemimoduleCat.MonoidalCategory.tensorObj W X) Y Z).hom ≫ (SemimoduleCat.MonoidalCategory.associator W X (SemimoduleCat.MonoidalCategory.tensorObj Y Z)).hom := by
  ext : 1
  apply TensorProduct.ext_fourfold
  intro w x y z
  rfl

