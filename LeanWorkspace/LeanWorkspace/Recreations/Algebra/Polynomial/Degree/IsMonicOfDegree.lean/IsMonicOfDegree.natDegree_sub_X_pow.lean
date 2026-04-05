import Mathlib

variable {R : Type*}

variable [Ring R]

theorem IsMonicOfDegree.natDegree_sub_X_pow {p : R[X]} {n : ℕ} (hn : n ≠ 0)
    (hp : IsMonicOfDegree p n) :
    (p - X ^ n).natDegree < n := by
  obtain ⟨q, hq₁, hq₂⟩ := hp.exists_natDegree_lt hn
  simpa [hq₁]

