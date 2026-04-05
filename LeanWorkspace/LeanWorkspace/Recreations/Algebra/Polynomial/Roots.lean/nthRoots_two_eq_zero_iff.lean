import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem nthRoots_two_eq_zero_iff {r : R} : Polynomial.nthRoots 2 r = 0 ↔ ¬IsSquare r := by
  simp_rw [isSquare_iff_exists_sq, eq_zero_iff_forall_notMem, Polynomial.mem_nthRoots (by simp : 0 < 2),
    ← not_exists, eq_comm]

