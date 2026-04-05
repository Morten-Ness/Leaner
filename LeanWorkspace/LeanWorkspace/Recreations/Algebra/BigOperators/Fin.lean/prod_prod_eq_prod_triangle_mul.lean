import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

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


theorem prod_prod_eq_prod_triangle_mul (f : Fin (n + 1) → Fin n → M) :
    ∏ i, ∏ j, f i j = ∏ i : Fin n, ∏ j ≥ i, (f i.castSucc j * f j.succ i) := calc
  _ = (∏ i, ∏ j with i ≤ j.castSucc, f i j) * ∏ i, ∏ j with j.castSucc < i, f i j := by
    simp only [← Finset.prod_mul_distrib, ← not_le, Finset.prod_filter_mul_prod_filter_not]
  _ = (∏ i, ∏ j ≥ i, f i.castSucc j) * ∏ i, ∏ j ≤ i, f i.succ j := by
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_succ]
    simp [Finset.filter_le_eq_Ici, Finset.filter_ge_eq_Iic]
  _ = (∏ i, ∏ j ≥ i, f i.castSucc j) * ∏ i, ∏ j ≥ i, f j.succ i := by
    congr 1
    apply Finset.prod_comm'
    simp
  _ = ∏ i : Fin n, ∏ j ≥ i, (f i.castSucc j * f j.succ i) := by
    simp only [Finset.prod_mul_distrib]

