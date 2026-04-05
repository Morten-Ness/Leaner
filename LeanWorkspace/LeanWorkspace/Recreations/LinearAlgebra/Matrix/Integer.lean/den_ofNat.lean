import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem den_ofNat [DecidableEq m] (a : ℕ) [a.AtLeastTwo] :
    (ofNat(a) : Matrix m m ℚ).den = 1 := Matrix.den_natCast a

