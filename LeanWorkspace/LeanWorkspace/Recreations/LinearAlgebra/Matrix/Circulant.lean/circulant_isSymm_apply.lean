import Mathlib

variable {α β n R : Type*}

theorem circulant_isSymm_apply [SubtractionMonoid n] {v : n → α} (h : (Matrix.circulant v).IsSymm)
    (i : n) : v (-i) = v i := Matrix.circulant_isSymm_iff.1 h i

