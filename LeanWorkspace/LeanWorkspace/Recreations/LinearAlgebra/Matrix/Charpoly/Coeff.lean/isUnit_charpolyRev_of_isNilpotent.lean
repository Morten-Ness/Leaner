import Mathlib

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem isUnit_charpolyRev_of_isNilpotent (hM : IsNilpotent M) :
    IsUnit M.charpolyRev := by
  obtain ⟨k, hk⟩ := hM
  replace hk : 1 - (X : R[X]) • M.map C ∣ 1 := by
    convert one_sub_dvd_one_sub_pow ((X : R[X]) • M.map C) k
    rw [← C.mapMatrix_apply, smul_pow, ← map_pow, hk, map_zero, smul_zero, sub_zero]
  apply isUnit_of_dvd_one
  rw [← det_one (R := R[X]) (n := n)]
  exact map_dvd detMonoidHom hk

