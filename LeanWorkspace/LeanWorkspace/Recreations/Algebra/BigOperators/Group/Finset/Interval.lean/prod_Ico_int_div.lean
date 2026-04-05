import Mathlib

theorem prod_Ico_int_div (b : ℕ) {α : Type*} [CommGroup α] (f : ℤ → α) :
    ∏ n ∈ Ico (-b : ℤ) b, f n / f (n + 1) = f (-b) / f b := by
  induction b with
  | zero => simp
  | succ b ihb =>
    simp only [Nat.cast_add_one, Ico_succ_succ]
    rw [prod_union (by simp), prod_insert (by grind), prod_singleton, ihb, ← mul_assoc, mul_div]
    simp [mul_comm, mul_div, ← mul_assoc]

