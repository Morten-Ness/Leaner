import Mathlib

variable {α β n R : Type*}

theorem Fin.circulant_mul [NonUnitalNonAssocSemiring α] :
    ∀ {n} (v w : Fin n → α), Matrix.circulant v * Matrix.circulant w = Matrix.circulant (Matrix.circulant v *ᵥ w)
  | 0 => by simp [eq_iff_true_of_subsingleton]
  | _ + 1 => Matrix.circulant_mul
