import Mathlib

variable {R : Type u} {α : Type*}

variable [CommSemiring R] [LinearOrder R] {a d : R}

theorem max_mul_mul_le_max_mul_max [PosMulMono R] [MulPosMono R] (b c : R) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    max (a * b) (d * c) ≤ max a c * max d b := have ba : b * a ≤ max d b * max c a := by
    gcongr
    exacts [ha, hd.trans <| le_max_left d b, le_max_right d b, le_max_right c a]
  have cd : c * d ≤ max a c * max b d :=
    mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c))
  max_le (by simpa [mul_comm, max_comm] using ba) (by simpa [mul_comm, max_comm] using cd)

