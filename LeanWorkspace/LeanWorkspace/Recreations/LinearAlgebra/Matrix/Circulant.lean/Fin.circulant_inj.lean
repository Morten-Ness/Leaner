import Mathlib

variable {α β n R : Type*}

theorem Fin.circulant_inj {n} {v w : Fin n → α} : Matrix.circulant v = Matrix.circulant w ↔ v = w := (Matrix.Fin.circulant_injective n).eq_iff

