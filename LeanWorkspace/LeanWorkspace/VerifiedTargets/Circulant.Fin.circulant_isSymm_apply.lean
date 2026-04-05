import Mathlib

variable {α β n R : Type*}

theorem Fin.circulant_isSymm_apply {n} {v : Fin n → α} (h : (Matrix.circulant v).IsSymm) (i : Fin n) :
    v (-i) = v i := Matrix.Fin.circulant_isSymm_iff.1 h i

