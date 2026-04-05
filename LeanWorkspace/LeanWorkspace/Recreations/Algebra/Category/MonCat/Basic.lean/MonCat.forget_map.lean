import Mathlib

theorem forget_map {X Y : MonCat} (f : X ⟶ Y) :
    (forget MonCat).map f = (f : _ → _) := rfl

