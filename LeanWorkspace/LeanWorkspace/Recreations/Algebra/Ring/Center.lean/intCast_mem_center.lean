import Mathlib

variable {M : Type*}

theorem intCast_mem_center [NonAssocRing M] (n : ℤ) : (n : M) ∈ Set.center M where
  comm _ := by rw [commute_iff_eq, Int.commute_cast]
  left_assoc _ _ := match n with
    | (n : ℕ) => by rw [Int.cast_natCast, (Set.natCast_mem_center _ n).left_assoc _ _]
    | Int.negSucc n => by
      rw [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, add_mul, add_mul, add_mul,
        neg_mul, one_mul, neg_mul 1, one_mul, ← neg_mul, add_right_inj, neg_mul,
        (Set.natCast_mem_center _ n).left_assoc _ _, neg_mul, neg_mul]
  right_assoc _ _ := match n with
    | (n : ℕ) => by rw [Int.cast_natCast, (Set.natCast_mem_center _ n).right_assoc _ _]
    | Int.negSucc n => by
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
        rw [mul_add, mul_add, mul_add, mul_neg, mul_one, mul_neg, mul_neg, mul_one, mul_neg,
          add_right_inj, (Set.natCast_mem_center _ n).right_assoc _ _, mul_neg, mul_neg]

