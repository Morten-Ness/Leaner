import Mathlib

variable {α β R n m : Type*}

theorem isDiag_smul_one (n) [MulZeroOneClass α] [DecidableEq n] (k : α) :
    (k • (1 : Matrix n n α)).IsDiag := Matrix.isDiag_one.smul k

