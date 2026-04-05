import Mathlib

variable {R : Type*} [CommRing R]

theorem eq_quo_mul_pow_add_sum_rem_mul_pow [Nontrivial R] (f : R[X]) {g : R[X]} (hg : g.Monic)
    (n : ℕ) : ∃ (q : R[X]) (r : Fin n → R[X]), (∀ i, (r i).degree < g.degree) ∧
      f = q * g ^ n + ∑ i, r i * g ^ i.1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨q, r, hr, hf⟩ := ih
    refine ⟨q /ₘ g, Fin.snoc r (q %ₘ g), fun i => ?_, hf.trans ?_⟩
    · cases i using Fin.lastCases with
      | cast i => simpa using hr i
      | last => simpa using degree_modByMonic_lt q hg
    · rw [Fin.sum_univ_castSucc, ← add_rotate', Fin.snoc_last, Fin.val_last,
        ← add_assoc, pow_succ', ← mul_assoc, ← add_mul, mul_comm (q /ₘ g) g,
        modByMonic_add_div q]
      simp

