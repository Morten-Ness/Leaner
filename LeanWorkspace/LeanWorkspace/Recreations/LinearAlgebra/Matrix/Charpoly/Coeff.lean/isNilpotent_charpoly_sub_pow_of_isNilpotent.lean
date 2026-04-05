import Mathlib

open scoped Ring Polynomial

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem isNilpotent_charpoly_sub_pow_of_isNilpotent (hM : IsNilpotent M) :
    IsNilpotent (M.charpoly - Polynomial.X ^ (Fintype.card n)) := by
  nontriviality R
  let p : R[X] := M.charpolyRev
  have hp : p - 1 = Polynomial.X * (p /ₘ Polynomial.X) := by
    conv_lhs => rw [← modByMonic_add_div p Polynomial.X]
    simp [p, modByMonic_X]
  have : IsNilpotent (p /ₘ Polynomial.X) :=
    (Polynomial.isUnit_iff'.mp (Matrix.isUnit_charpolyRev_of_isNilpotent hM)).2
  have aux : (M.charpoly - Polynomial.X ^ (Fintype.card n)).natDegree ≤ M.charpoly.natDegree :=
    le_trans (natDegree_sub_le _ _) (by simp)
  rw [← isNilpotent_reflect_iff aux, reflect_sub, ← reverse, M.reverse_charpoly]
  simpa [p, hp]

