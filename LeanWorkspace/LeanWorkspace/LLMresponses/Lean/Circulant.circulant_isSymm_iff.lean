FAIL
import Mathlib

variable {α β n R : Type*}

theorem circulant_isSymm_iff [SubtractionMonoid n] {v : n → α} :
    (Matrix.circulant v).IsSymm ↔ ∀ i, v (-i) = v i := by
  constructor
  · intro hs i
    have h := hs i 0
    simpa [Matrix.IsSymm, Matrix.circulant_apply] using h
  · intro h
    intro i j
    have hij := h (j - i)
    simpa [Matrix.IsSymm, Matrix.circulant_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hij
