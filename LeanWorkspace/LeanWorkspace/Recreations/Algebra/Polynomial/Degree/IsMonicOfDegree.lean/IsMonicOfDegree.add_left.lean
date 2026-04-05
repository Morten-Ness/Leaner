import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem IsMonicOfDegree.add_left {p q : R[X]} {n : ℕ} (hp : p.natDegree < n)
    (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p + q) n := by
  rw [add_comm]
  exact hq.add_right hp

