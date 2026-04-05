import Mathlib

variable {m n R A : Type*} [CommRing R] [Fintype m] [Fintype n] [CommRing A] [IsDomain A]
  {M : Matrix m n R}

theorem Nondegenerate.exists_not_ortho_of_ne_zero' {M : Matrix m n R} (hM : Nondegenerate M)
    {w : n → R} (hw : w ≠ 0) : ∃ v, v ⬝ᵥ M *ᵥ w ≠ 0 := not_forall.mp (mt hM.eq_zero_of_ortho' hw)

