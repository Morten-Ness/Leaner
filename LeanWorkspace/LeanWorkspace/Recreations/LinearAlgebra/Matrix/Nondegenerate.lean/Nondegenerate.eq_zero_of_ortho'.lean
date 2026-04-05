import Mathlib

variable {m n R A : Type*} [CommRing R] [Fintype m] [Fintype n] [CommRing A] [IsDomain A]
  {M : Matrix m n R}

theorem Nondegenerate.eq_zero_of_ortho' {M : Matrix m n R} (hM : Nondegenerate M) {w : n → R}
    (hw : ∀ v, v ⬝ᵥ M *ᵥ w = 0) : w = 0 := (Matrix.nondegenerate_def.mp hM).2 w hw

