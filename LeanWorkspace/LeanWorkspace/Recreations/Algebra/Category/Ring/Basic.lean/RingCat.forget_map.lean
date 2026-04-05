import Mathlib

theorem forget_map {R S : RingCat} (f : R ⟶ S) :
    (forget RingCat).map f = f := rfl

