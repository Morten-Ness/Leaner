import Mathlib

variable {ι M : Type*}

variable [Monoid M] {n : ℕ}

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


theorem partialProd_contractNth {G : Type*} [Monoid G] {n : ℕ}
    (g : Fin (n + 1) → G) (a : Fin (n + 1)) :
    Fin.partialProd (contractNth a (· * ·) g) = Fin.partialProd g ∘ a.succ.succAbove := by
  ext i
  refine inductionOn i ?_ ?_
  · simp
  · intro i hi
    simp only [Function.comp_apply, succ_succAbove_succ] at *
    rw [Fin.partialProd_succ, Fin.partialProd_succ, hi]
    rcases lt_trichotomy (i : ℕ) a with (h | h | h)
    · rw [succAbove_of_castSucc_lt, contractNth_apply_of_lt _ _ _ _ h,
        succAbove_of_castSucc_lt] <;>
      simp only [lt_def, val_castSucc, val_succ] <;>
      lia
    · rw [succAbove_of_castSucc_lt, contractNth_apply_of_eq _ _ _ _ h,
        succAbove_of_le_castSucc, castSucc_succ, Fin.partialProd_succ, mul_assoc] <;>
      simp only [castSucc_lt_succ_iff, le_def, val_castSucc] <;>
      lia
    · rw [succAbove_of_le_castSucc, succAbove_of_le_castSucc, contractNth_apply_of_gt _ _ _ _ h,
        castSucc_succ] <;>
      simp only [le_def, val_succ, val_castSucc] <;>
      lia

