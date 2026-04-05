import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem mul_neg_geom_sum (x : R) (n : ℕ) : ((1 - x) * ∑ i ∈ range n, x ^ i) = 1 - x ^ n := op_injective <| by simpa using geom_sum_mul_neg (op x) n

protected lemma Commute.mul_geom_sum₂_Ico (h : Commute x y) {m n : ℕ}
    (hmn : m ≤ n) :
    ((x - y) * ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) := by
  rw [sum_Ico_eq_sub _ hmn]
  have :
    ∑ k ∈ range m, x ^ k * y ^ (n - 1 - k) =
      ∑ k ∈ range m, x ^ k * (y ^ (n - m) * y ^ (m - 1 - k)) := by
    refine Finset.sum_congr rfl fun j j_in => ?_
    rw [← pow_add]
    congr
    rw [mem_range] at j_in
    lia
  rw [this]
  simp_rw [pow_mul_comm y (n - m) _]
  simp_rw [← mul_assoc]
  rw [← sum_mul, mul_sub, h.mul_geom_sum₂, ← mul_assoc, h.mul_geom_sum₂, sub_mul, ← pow_add,
    add_tsub_cancel_of_le hmn, sub_sub_sub_cancel_right (x ^ n) (x ^ m * y ^ (n - m)) (y ^ n)]

protected lemma Commute.geom_sum₂_succ_eq (h : Commute x y) {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) =
      x ^ n + y * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) := by
  simp_rw [mul_sum, sum_range_succ_comm, tsub_self, pow_zero, mul_one, add_right_inj, ← mul_assoc,
    (h.symm.pow_right _).eq, mul_assoc, ← pow_succ']
  refine Finset.sum_congr rfl fun i hi => ?_
  suffices n - 1 - i + 1 = n - i by rw [this]
  rw [Finset.mem_range] at hi
  lia

protected lemma Commute.geom_sum₂_Ico_mul (h : Commute x y) {m n : ℕ}
    (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ (n - m) * x ^ m := by
  apply op_injective
  simp only [op_sub, op_mul, op_pow, op_sum]
  have : (∑ k ∈ Ico m n, MulOpposite.op y ^ (n - 1 - k) * MulOpposite.op x ^ k) =
      ∑ k ∈ Ico m n, MulOpposite.op x ^ k * MulOpposite.op y ^ (n - 1 - k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hp := Commute.pow_pow (Commute.op h.symm) (n - 1 - k) k
    simpa [Commute, SemiconjBy] using hp
  simp only [this]
  convert (Commute.op h).mul_geom_sum₂_Ico hmn

