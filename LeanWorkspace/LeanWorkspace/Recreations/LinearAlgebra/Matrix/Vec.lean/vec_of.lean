import Mathlib

theorem vec_of (f : m → n → R) : Matrix.vec (of f) = Function.uncurry (flip f) := rfl

