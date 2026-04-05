import Mathlib

theorem forget_map {R S : CommSemiRingCat} (f : R ⟶ S) :
    (forget CommSemiRingCat).map f = f := rfl

