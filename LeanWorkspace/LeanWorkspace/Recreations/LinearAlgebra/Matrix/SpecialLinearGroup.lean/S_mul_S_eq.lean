import Mathlib

theorem S_mul_S_eq : (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) * ModularGroup.S = -1 := by
  simp only [ModularGroup.S, Int.reduceNeg, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
    vecMul_cons, head_cons, zero_smul, tail_cons, neg_smul, one_smul, neg_cons, neg_zero, neg_empty,
    empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply]
  exact Eq.symm (eta_fin_two (-1))

