import Mathlib

section

variable {α β n R : Type*}

theorem Fin.circulant_inj {n} {v w : Fin n → α} : Matrix.circulant v = Matrix.circulant w ↔ v = w := (Matrix.Fin.circulant_injective n).eq_iff

end

section

variable {α β n R : Type*}

theorem Fin.circulant_isSymm_apply {n} {v : Fin n → α} (h : (Matrix.circulant v).IsSymm) (i : Fin n) :
    v (-i) = v i := Matrix.Fin.circulant_isSymm_iff.1 h i

end

section

variable {α β n R : Type*}

theorem circulant_injective [SubtractionMonoid n] :
    Function.Injective (Matrix.circulant : (n → α) → Matrix n n α) := by
  intro v w h
  ext k
  rw [← Matrix.circulant_col_zero_eq v, ← Matrix.circulant_col_zero_eq w, h]

end

section

variable {α β n R : Type*}

theorem circulant_isSymm_iff [SubtractionMonoid n] {v : n → α} :
    (Matrix.circulant v).IsSymm ↔ ∀ i, v (-i) = v i := by
  rw [Matrix.IsSymm, Matrix.transpose_circulant, Matrix.circulant_inj, funext_iff]

end
