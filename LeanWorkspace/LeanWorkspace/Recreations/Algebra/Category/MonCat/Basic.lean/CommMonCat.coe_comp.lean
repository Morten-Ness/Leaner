import Mathlib

theorem coe_comp {X Y Z : CommMonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

