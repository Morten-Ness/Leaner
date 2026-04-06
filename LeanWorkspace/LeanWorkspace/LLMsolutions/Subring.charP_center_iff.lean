FAIL
import Mathlib

theorem charP_center_iff {R : Type u} [Ring R] {p : ℕ} :
    CharP (Subring.center R) p ↔ CharP R p := by
  simpa [Subring.charP_iff] using (Subring.center R)
