import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem num_ofNat [DecidableEq m] (a : ℕ) [a.AtLeastTwo] :
    (ofNat(a) : Matrix m m ℚ).num = a := Matrix.num_natCast a

