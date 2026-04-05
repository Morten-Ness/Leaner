import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem neg_one_geom_sum {n : ℕ} : ∑ i ∈ range n, (-1 : R) ^ i = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ k hk =>
    simp only [geom_sum_succ', Nat.even_add_one, hk]
    split_ifs with h
    · rw [h.neg_one_pow, add_zero]
    · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow, neg_add_cancel]

protected lemma Commute.geom_sum₂_mul (h : Commute x y) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  have := (h.sub_left (Commute.refl y)).geom_sum₂_mul_add n
  rw [sub_add_cancel] at this
  rw [← this, add_sub_cancel_right]

