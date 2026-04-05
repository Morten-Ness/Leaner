import Mathlib

theorem coe_comp {X Y Z : CommGrpCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

