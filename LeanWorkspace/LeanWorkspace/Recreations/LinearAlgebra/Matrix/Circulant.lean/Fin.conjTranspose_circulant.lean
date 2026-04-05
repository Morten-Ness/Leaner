import Mathlib

variable {α β n R : Type*}

theorem Fin.conjTranspose_circulant [Star α] :
    ∀ {n} (v : Fin n → α), (Matrix.circulant v)ᴴ = Matrix.circulant (star fun i => v (-i))
  | 0 => by simp [eq_iff_true_of_subsingleton]
  | _ + 1 => Matrix.conjTranspose_circulant
