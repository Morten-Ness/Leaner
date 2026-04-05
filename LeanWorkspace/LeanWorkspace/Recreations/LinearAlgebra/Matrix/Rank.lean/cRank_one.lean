import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem cRank_one [Nontrivial R] [DecidableEq m] :
    (Matrix.cRank (1 : Matrix m m R)) = lift.{uR} #m := by
  have h : LinearIndependent R (1 : Matrix m m R)ᵀ := by
    convert Pi.linearIndependent_single_one m R
    simp [funext_iff, Matrix.one_eq_pi_single]
  rw [Matrix.cRank, rank_span h, ← lift_umax, ← Cardinal.mk_range_eq_of_injective h.injective, lift_id']

