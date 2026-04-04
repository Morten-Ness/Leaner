import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem medial_reindex {m n : ℕ} [NeZero m] [NeZero n]
    [CharZero k] (s : Affine.Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).medial = s.medial.reindex e := by
  ext i
  simp [Affine.Simplex.medial_points]

