import Mathlib

theorem forget_map {R S : SemiRingCat} (f : R ⟶ S) :
    (forget SemiRingCat).map f = f := rfl

