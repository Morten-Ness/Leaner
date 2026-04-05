import Mathlib

section

variable {R : Type u} [CommSemiring R]

theorem braiding_naturality {X₁ X₂ Y₁ Y₂ : SemimoduleCat.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g) ≫ (Y₁.braiding Y₂).hom = (X₁.braiding X₂).hom ≫ (g ⊗ₘ f) := by
  ext : 1
  apply TensorProduct.ext'
  intro x y
  rfl

end

section

variable {R : Type u} [CommSemiring R]

theorem braiding_naturality_left {X Y : SemimoduleCat R} (f : X ⟶ Y) (Z : SemimoduleCat R) :
    f ▷ Z ≫ (SemimoduleCat.braiding Y Z).hom = (SemimoduleCat.braiding X Z).hom ≫ Z ◁ f := by
  simp_rw [← id_tensorHom]
  apply SemimoduleCat.MonoidalCategory.braiding_naturality

end

section

variable {R : Type u} [CommSemiring R]

theorem braiding_naturality_right (X : SemimoduleCat R) {Y Z : SemimoduleCat R} (f : Y ⟶ Z) :
    X ◁ f ≫ (SemimoduleCat.braiding X Z).hom = (SemimoduleCat.braiding X Y).hom ≫ f ▷ X := by
  simp_rw [← id_tensorHom]
  apply SemimoduleCat.MonoidalCategory.braiding_naturality

end

section

variable {R : Type u} [CommSemiring R]

theorem hexagon_forward (X Y Z : SemimoduleCat.{u} R) :
    (α_ X Y Z).hom ≫ (SemimoduleCat.braiding X _).hom ≫ (α_ Y Z X).hom =
      (SemimoduleCat.braiding X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (SemimoduleCat.braiding X Z).hom := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

end

section

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

end
