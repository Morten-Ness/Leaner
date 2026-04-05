import Mathlib

theorem prod_Icc_of_even_eq_range {α : Type*} [CommGroup α] {f : ℤ → α} (hf : f.Even) (N : ℕ) :
    ∏ m ∈ Icc (-N : ℤ) N, f m = (∏ m ∈ range (N + 1), f m) ^ 2 / f 0 := by
  induction N with
  | zero => simp [sq]
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one, Icc_succ_succ, prod_union (by simp), prod_pair (by lia), ih,
      prod_range_succ _ (N + 1), hf, ← pow_two, div_mul_eq_mul_div, ← mul_pow, Nat.cast_succ]

