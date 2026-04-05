import Mathlib

variable {α β n R : Type*}

theorem Fin.transpose_circulant : ∀ {n} (v : Fin n → α), (Matrix.circulant v)ᵀ = Matrix.circulant fun i => v (-i)
  | 0 => by simp [eq_iff_true_of_subsingleton]
  | _ + 1 => Matrix.transpose_circulant
