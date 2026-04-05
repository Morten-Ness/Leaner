import Mathlib

variable {ι M : Type*}

variable [CommMonoid M]

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


theorem prod_take_ofFn {n : ℕ} (f : Fin n → M) (i : ℕ) :
    ((ofFn f).take i).prod = ∏ j with j.val < i, f j := by
  induction i with
  | zero =>
    simp
  | succ i IH =>
    by_cases h : i < n
    · have : i < length (ofFn f) := by rwa [length_ofFn]
      rw [prod_take_succ _ _ this]
      have A : ({j | j.val < i + 1} : Finset (Fin n)) =
          insert ⟨i, h⟩ ({j | Fin.val j < i} : Finset (Fin n)) := by grind
      grind
    · have A : (ofFn f).take i = (ofFn f).take i.succ := by
        rw [← length_ofFn (f := f)] at h
        have : length (ofFn f) ≤ i := not_lt.mp h
        rw [take_of_length_le this, take_of_length_le (le_trans this (Nat.le_succ _))]
      have B : ∀ j : Fin n, ((j : ℕ) < i.succ) = ((j : ℕ) < i) := by
        intro j
        have : (j : ℕ) < i := lt_of_lt_of_le j.2 (not_lt.mp h)
        simp [this, lt_trans this (Nat.lt_succ_self _)]
      simp [← A, B, IH]

