import Mathlib

variable {α β n R : Type*}

theorem Fin.circulant_mul_comm [CommMagma α] [AddCommMonoid α] :
    ∀ {n} (v w : Fin n → α), Matrix.circulant v * Matrix.circulant w = Matrix.circulant w * Matrix.circulant v
  | 0 => by simp
  | _ + 1 => Matrix.circulant_mul_comm
