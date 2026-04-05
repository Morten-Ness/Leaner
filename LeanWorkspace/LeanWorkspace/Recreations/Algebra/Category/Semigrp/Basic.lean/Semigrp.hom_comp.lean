import Mathlib

theorem hom_comp {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

