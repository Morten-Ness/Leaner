import Mathlib

theorem star_vec [Star R] (x : Matrix m n R) :
    star x.vec = (x.map star).vec := rfl

