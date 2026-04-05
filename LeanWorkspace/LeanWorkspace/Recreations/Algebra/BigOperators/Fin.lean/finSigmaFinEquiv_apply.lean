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


theorem finSigmaFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (k : (i : Fin m) × Fin (n i)) :
    (finSigmaFinEquiv k : ℕ) = ∑ i : Fin k.1, n (Fin.castLE k.1.2.le i) + k.2 := by
  induction m with
  | zero => exact k.fst.elim0
  | succ m ih =>
  rcases k with ⟨⟨iv, hi⟩, j⟩
  rw [finSigmaFinEquiv]
  unfold finSumFinEquiv
  simp only [Equiv.coe_fn_mk, Equiv.sigmaCongrLeft, Equiv.coe_fn_symm_mk, Equiv.trans_def,
    Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  by_cases him : iv < m
  · conv in Sigma.mk _ _ =>
      equals ⟨Sum.inl ⟨iv, him⟩, j⟩ => simp [Fin.addCases, him]
    simpa using ih _
  · replace him := Nat.eq_of_lt_succ_of_not_lt hi him
    subst him
    conv in Sigma.mk _ _ =>
      equals ⟨Sum.inr 0, j⟩ => simp [Fin.addCases, Fin.natAdd]
    simp
    rfl

