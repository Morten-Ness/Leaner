import Mathlib

variable {R : Type u} [CommSemiring R]

theorem hexagon_reverse (X Y Z : SemimoduleCat.{u} R) :
    (α_ X Y Z).inv ≫ (SemimoduleCat.braiding _ Z).hom ≫ (α_ Z X Y).inv =
      X ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).inv ≫ (X.braiding Z).hom ▷ Y := by
  apply (cancel_epi (α_ X Y Z).hom).1
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

attribute [local ext] TensorProduct.ext

