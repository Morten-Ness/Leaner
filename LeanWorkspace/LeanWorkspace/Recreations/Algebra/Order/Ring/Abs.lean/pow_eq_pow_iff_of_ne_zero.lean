import Mathlib

variable {α : Type*}

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {n : ℕ}

private def geomSum : ℕ → α
  | 0 => 1
  | n + 1 => a * geomSum n + b ^ (n + 1)

private theorem abs_geomSum_le [IsOrderedRing α] : |geomSum a b n| ≤ (n + 1) * max |a| |b| ^ n := by
  induction n with | zero => simp [geomSum] | succ n ih => ?_
  refine (abs_add_le ..).trans ?_
  rw [abs_mul, abs_pow, Nat.cast_succ, add_one_mul]
  refine add_le_add ?_ (pow_le_pow_left₀ (abs_nonneg _) le_sup_right _)
  rw [pow_succ, ← mul_assoc, mul_comm |a|]
  exact mul_le_mul ih le_sup_left (abs_nonneg _) (mul_nonneg
    (@Nat.cast_succ α .. ▸ Nat.cast_nonneg _) <| pow_nonneg ((abs_nonneg _).trans le_sup_left) _)


omit [LinearOrder α] in
private theorem pow_sub_pow_eq_sub_mul_geomSum :
    a ^ (n + 1) - b ^ (n + 1) = (a - b) * geomSum a b n := by
  induction n with | zero => simp [geomSum] | succ n ih => ?_
  rw [geomSum, mul_add, mul_comm a, ← mul_assoc, ← ih,
    sub_mul, sub_mul, ← pow_succ, ← pow_succ', mul_comm, sub_add_sub_cancel]


theorem pow_eq_pow_iff_of_ne_zero (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n := match n.even_xor_odd with
  | .inl hne => by simp only [*, and_true, ← abs_eq_abs,
    ← pow_left_inj₀ (abs_nonneg a) (abs_nonneg b) hn, pow_abs hne.1]
  | .inr hn => by simp [hn, (hn.1.strictMono_pow (R := R)).injective.eq_iff]

