import Mathlib

variable {R : Type*}

variable [Ring R]

theorem IsMonicOfDegree.natDegree_sub_lt {p q : R[X]} {n : ℕ} (hn : n ≠ 0) (hp : IsMonicOfDegree p n)
    (hq : IsMonicOfDegree q n) :
    (p - q).natDegree < n := by
  rw [← sub_sub_sub_cancel_right p q (X ^ n)]
  replace hp := hp.natDegree_sub_X_pow hn
  replace hq := hq.natDegree_sub_X_pow hn
  rw [← Nat.le_sub_one_iff_lt (Nat.zero_lt_of_ne_zero hn)] at hp hq ⊢
  exact (natDegree_sub_le_iff_left hq).mpr hp

