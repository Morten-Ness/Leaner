import Mathlib

theorem forget_map {X Y : CommGrpCat} (f : X ⟶ Y) :
    (forget CommGrpCat).map f = (f : X → Y) := rfl

