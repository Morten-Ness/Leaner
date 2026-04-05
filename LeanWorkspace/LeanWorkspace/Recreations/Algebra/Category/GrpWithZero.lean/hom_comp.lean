import Mathlib

theorem hom_comp {X Y Z : GrpWithZero} {f : X ⟶ Y} {g : Y ⟶ Z} :
    ConcreteCategory.hom (f ≫ g) = g.comp f := rfl

