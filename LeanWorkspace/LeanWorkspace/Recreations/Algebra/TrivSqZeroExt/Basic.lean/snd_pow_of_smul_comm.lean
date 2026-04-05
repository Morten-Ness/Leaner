import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_pow_of_smul_comm [Monoid R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : tsze R M) (n : ℕ)
    (h : x.snd <• x.fst = x.fst •> x.snd) : TrivSqZeroExt.snd (x ^ n) = n • x.fst ^ n.pred •> x.snd := by
  simp_rw [TrivSqZeroExt.snd_pow_eq_sum, ← smul_comm (_ : R) (_ : Rᵐᵒᵖ), aux, smul_smul, ← pow_add]
  match n with
  | 0 => rw [Nat.pred_zero, pow_zero, List.range_zero, zero_smul, List.map_nil, List.sum_nil]
  | (Nat.succ n) =>
    simp_rw [Nat.pred_succ]
    exact (List.sum_eq_card_nsmul _ (x.fst ^ n • x.snd) (by grind)).trans
      (by rw [List.length_map, List.length_range])
where
  aux : ∀ n : ℕ, x.snd <• x.fst ^ n = x.fst ^ n •> x.snd := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, op_mul, mul_smul, mul_smul, ← h, smul_comm (_ : R) (op x.fst) x.snd, ih]

