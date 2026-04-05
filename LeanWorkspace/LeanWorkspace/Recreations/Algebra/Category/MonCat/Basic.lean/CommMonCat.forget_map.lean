import Mathlib

theorem forget_map {X Y : CommMonCat} (f : X ⟶ Y) :
    (forget CommMonCat).map f = (f : X → Y) := rfl

