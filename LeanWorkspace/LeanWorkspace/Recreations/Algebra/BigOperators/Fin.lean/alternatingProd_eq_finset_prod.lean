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


theorem alternatingProd_eq_finset_prod {G : Type*} [DivisionCommMonoid G] :
    ∀ (L : List G), alternatingProd L = ∏ i : Fin L.length, L[i] ^ (-1 : ℤ) ^ (i : ℕ)
  | [] => by
    rw [alternatingProd, Finset.prod_eq_one]
    rintro ⟨i, ⟨⟩⟩
  | g::[] => by
    change g = ∏ i : Fin 1, [g][i] ^ (-1 : ℤ) ^ (i : ℕ)
    rw [Fin.prod_univ_succ]; simp
  | g::h::L =>
    calc g * h⁻¹ * L.alternatingProd
      = g * h⁻¹ * ∏ i : Fin L.length, L[i] ^ (-1 : ℤ) ^ (i : ℕ) := congr_arg _ (alternatingProd_eq_finset_prod _)
    _ = ∏ i : Fin (L.length + 2), (g::h::L)[i] ^ (-1 : ℤ) ^ (i : ℕ) := by
        { rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_assoc]
          simp [pow_add]}

