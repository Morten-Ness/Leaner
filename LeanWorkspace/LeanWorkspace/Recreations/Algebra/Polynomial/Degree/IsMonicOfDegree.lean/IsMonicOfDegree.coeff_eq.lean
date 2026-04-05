import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem IsMonicOfDegree.coeff_eq {p q : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n)
    (hq : IsMonicOfDegree q n) {m : ℕ} (hm : n ≤ m) :
    p.coeff m = q.coeff m := by
  nontriviality R
  rw [Polynomial.isMonicOfDegree_iff] at hp hq
  rcases eq_or_lt_of_le hm with rfl | hm
  · rw [hp.2, hq.2]
  · replace hp : p.natDegree < m := hp.1.trans_lt hm
    replace hq : q.natDegree < m := hq.1.trans_lt hm
    rw [coeff_eq_zero_of_natDegree_lt hp, coeff_eq_zero_of_natDegree_lt hq]

