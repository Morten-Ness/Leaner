import Mathlib

variable {R : Type*}

variable [Ring R]

theorem IsMonicOfDegree.sub {p q : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (hq : q.natDegree < n) :
    IsMonicOfDegree (p - q) n := by
  rw [sub_eq_add_neg]
  exact hp.add_right <| (natDegree_neg q) ▸ hq

