import Mathlib

theorem RingCat.forget_map_apply {R S : RingCat} (f : R ⟶ S)
    (x : (CategoryTheory.forget RingCat).obj R) :
    (forget _).map f x = f x := rfl

