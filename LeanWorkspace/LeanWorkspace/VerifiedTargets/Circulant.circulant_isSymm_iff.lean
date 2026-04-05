import Mathlib

variable {α β n R : Type*}

theorem circulant_isSymm_iff [SubtractionMonoid n] {v : n → α} :
    (Matrix.circulant v).IsSymm ↔ ∀ i, v (-i) = v i := by
  rw [Matrix.IsSymm, Matrix.transpose_circulant, Matrix.circulant_inj, funext_iff]

