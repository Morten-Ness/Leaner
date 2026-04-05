import Mathlib

variable {R : Type u} [CommSemiring R]

theorem hexagon_forward (X Y Z : SemimoduleCat.{u} R) :
    (α_ X Y Z).hom ≫ (SemimoduleCat.braiding X _).hom ≫ (α_ Y Z X).hom =
      (SemimoduleCat.braiding X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (SemimoduleCat.braiding X Z).hom := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

