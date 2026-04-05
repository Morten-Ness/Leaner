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


theorem partialProd_left_inv {G : Type*} [Group G] (f : Fin (n + 1) → G) :
    (f 0 • Fin.partialProd fun i : Fin n => (f i.castSucc)⁻¹ * f i.succ) = f := funext fun x => Fin.inductionOn x (by simp) fun x hx => by
    simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [Fin.partialProd_succ, ← mul_assoc, hx, mul_inv_cancel_left]

