import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem iterate_derivative_prod_X_sub_C {k : ℕ} {S : Finset R} (hk : k ≤ #S) :
    Polynomial.derivative^[k] (∏ a ∈ S, (Polynomial.X - Polynomial.C a)) =
    k.factorial * ∑ T ∈ S.powersetCard (#S - k), ∏ a ∈ T, (Polynomial.X - Polynomial.C a) := by
  classical
  induction k
  case zero => simp
  case succ k ind =>
    specialize ind (Nat.le_of_succ_le hk)
    nth_rewrite 1 [add_comm]
    rw [Function.iterate_add_apply, Function.iterate_one, ind, ← nsmul_eq_mul, Polynomial.derivative_smul,
      nsmul_eq_mul, Polynomial.derivative_sum, Nat.factorial_succ, mul_comm (k + 1), Nat.cast_mul, mul_assoc]
    congr 1
    calc
      ∑ T ∈ S.powersetCard (#S - k), Polynomial.derivative (∏ a ∈ T, (Polynomial.X - Polynomial.C a)) =
      ∑ T ∈ S.powersetCard (#S - k), ∑ i ∈ T, ∏ a ∈ T.erase i, (Polynomial.X - Polynomial.C a) := by
        congr! with T hT
        simp_rw [Polynomial.derivative_prod_finset, Polynomial.derivative_X_sub_C, mul_one]
      _ = ∑ (T ∈ S.powersetCard (#S - k)) (i ∈ S) with i ∈ T, ∏ a ∈ T.erase i, (Polynomial.X - Polynomial.C a) := by
        rw [← sum_finset_product']
        grind
      _ = ∑ (T ∈ S.powersetCard (#S - (k + 1))) (i ∈ S) with i ∉ T, ∏ a ∈ T, (Polynomial.X - Polynomial.C a) := by
        apply sum_bij' (fun ⟨T, i⟩ _ => ⟨T.erase i, i⟩) (fun ⟨T, i⟩ _ => ⟨insert i T, i⟩)
        · intro r hr; dsimp at hr ⊢; congr 1; grind
        · intro r hr; dsimp at hr ⊢; congr 1; grind
        all_goals grind
      _ = ∑ T ∈ S.powersetCard (#S - (k + 1)), ∑ i ∈ S \ T, ∏ a ∈ T, (Polynomial.X - Polynomial.C a) := by
        rw [← sum_finset_product']
        grind
      _ = (k + 1) * ∑ T ∈ S.powersetCard (#S - (k + 1)), ∏ a ∈ T, (Polynomial.X - Polynomial.C a) := by
        rw [mul_sum]
        congr! 1 with T hT
        simp [Finset.sum_const, show #(S \ T) = k + 1 by grind]
      _ = _ := by grind

