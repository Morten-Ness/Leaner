import Mathlib

theorem forget_map {R S : CommRingCat} (f : R ⟶ S) :
    (forget CommRingCat).map f = f := rfl

