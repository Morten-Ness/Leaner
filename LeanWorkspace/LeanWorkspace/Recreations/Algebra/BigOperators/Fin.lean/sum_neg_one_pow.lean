import Mathlib

variable {ι M : Type*}

private theorem prod_insertNth_go :
    ∀ n i (h : i < n + 1) x (p : Fin n → M), ∏ j, insertNth ⟨i, h⟩ x p j = x * ∏ j, p j
  | n, 0, h, x, p => by simp
  | 0, i, h, x, p => by simp [fin_one_eq_zero ⟨i, h⟩]
  | n + 1, i + 1, h, x, p => by
    obtain ⟨hd, tl, rfl⟩ := exists_cons p
    have i_lt := Nat.lt_of_succ_lt_succ h
    let i_fin : Fin (n + 1) := ⟨i, i_lt⟩
    rw [show ⟨i + 1, h⟩ = i_fin.succ from rfl]
    simp only [insertNth_succ_cons, Fin.prod_cons]
    rw [prod_insertNth_go n i i_lt x tl, mul_left_comm]


theorem sum_neg_one_pow (R : Type*) [Ring R] (m : ℕ) :
    (∑ n : Fin m, (-1) ^ n.1 : R) = if Even m then 0 else 1 := by
  induction m with
  | zero => simp
  | succ n IH =>
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, IH, Fin.val_last, Nat.even_add_one, ite_not]
    split_ifs with h
    · simp [*]
    · simp [(Nat.not_even_iff_odd.mp h).neg_pow]

