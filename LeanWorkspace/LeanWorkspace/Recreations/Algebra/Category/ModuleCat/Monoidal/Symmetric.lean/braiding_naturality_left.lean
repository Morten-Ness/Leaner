import Mathlib

variable {R : Type u} [CommSemiring R]

theorem braiding_naturality_left {X Y : SemimoduleCat R} (f : X ⟶ Y) (Z : SemimoduleCat R) :
    f ▷ Z ≫ (SemimoduleCat.braiding Y Z).hom = (SemimoduleCat.braiding X Z).hom ≫ Z ◁ f := by
  simp_rw [← id_tensorHom]
  apply SemimoduleCat.MonoidalCategory.braiding_naturality

