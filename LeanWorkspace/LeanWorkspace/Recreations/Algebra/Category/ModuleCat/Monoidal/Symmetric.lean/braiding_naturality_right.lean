import Mathlib

variable {R : Type u} [CommSemiring R]

theorem braiding_naturality_right (X : SemimoduleCat R) {Y Z : SemimoduleCat R} (f : Y ⟶ Z) :
    X ◁ f ≫ (SemimoduleCat.braiding X Z).hom = (SemimoduleCat.braiding X Y).hom ≫ f ▷ X := by
  simp_rw [← id_tensorHom]
  apply SemimoduleCat.MonoidalCategory.braiding_naturality

