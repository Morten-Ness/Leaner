import Mathlib

variable {α β : Type*}

theorem Nodup.le_nsmul_iff_le {s t : Multiset α} {n : ℕ} (h : s.Nodup) (hn : n ≠ 0) :
    s ≤ n • t ↔ s ≤ t := by
  classical simp [← h.le_dedup_iff_le, hn]

