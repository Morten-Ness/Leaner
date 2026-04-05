import Mathlib

theorem forget_map {X Y : MagmaCat} (f : X ⟶ Y) :
    (forget MagmaCat).map f = (f : _ → _) := rfl

