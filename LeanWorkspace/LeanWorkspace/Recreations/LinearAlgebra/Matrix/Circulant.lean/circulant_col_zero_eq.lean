import Mathlib

variable {α β n R : Type*}

theorem circulant_col_zero_eq [SubtractionMonoid n] (v : n → α) (i : n) : Matrix.circulant v i 0 = v i := congr_arg v (sub_zero _)

