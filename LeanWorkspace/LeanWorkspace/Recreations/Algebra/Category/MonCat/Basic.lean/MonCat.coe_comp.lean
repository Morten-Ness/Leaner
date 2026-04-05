import Mathlib

theorem coe_comp {X Y Z : MonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

