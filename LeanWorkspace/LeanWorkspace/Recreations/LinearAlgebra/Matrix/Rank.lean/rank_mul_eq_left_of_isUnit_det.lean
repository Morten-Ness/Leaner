import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem rank_mul_eq_left_of_isUnit_det [DecidableEq n]
    (A : Matrix n n R) (B : Matrix m n R) (hA : IsUnit A.det) :
    (B * A).rank = B.rank := by
  suffices Function.Surjective A.mulVecLin by
    rw [Matrix.rank, mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr this), ← Matrix.rank]
  intro v
  exact ⟨(A⁻¹).mulVecLin v, by simp [mul_nonsing_inv _ hA]⟩

