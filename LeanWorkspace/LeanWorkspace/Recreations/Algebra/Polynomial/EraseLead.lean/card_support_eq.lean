import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem card_support_eq {n : ℕ} :
    #f.support = n ↔
      ∃ (k : Fin n → ℕ) (x : Fin n → R) (_ : StrictMono k) (_ : ∀ i, x i ≠ 0),
        f = ∑ i, Polynomial.C (x i) * Polynomial.X ^ k i := by
  refine ⟨?_, fun ⟨k, x, hk, hx, hf⟩ => hf.symm ▸ Polynomial.card_support_eq' k x hk.injective hx⟩
  induction n generalizing f with
  | zero => exact fun hf => ⟨0, 0, fun x => x.elim0, fun x => x.elim0, card_support_eq_zero.mp hf⟩
  | succ n hn =>
    intro h
    obtain ⟨k, x, hk, hx, hf⟩ := hn (Polynomial.card_support_eraseLead' h)
    have H : ¬∃ k : Fin n, Fin.castSucc k = Fin.last n := by
      rintro ⟨i, hi⟩
      exact i.castSucc_lt_last.ne hi
    refine
      ⟨Function.extend Fin.castSucc k fun _ => f.natDegree,
        Function.extend Fin.castSucc x fun _ => f.leadingCoeff, ?_, ?_, ?_⟩
    · intro i j hij
      have hi : i ∈ Set.range (Fin.castSucc : Fin n → Fin (n + 1)) := by
        simp only [Fin.range_castSucc, Nat.succ_eq_add_one, Set.mem_setOf_eq]
        exact lt_of_lt_of_le hij (Nat.lt_succ_iff.mp j.2)
      obtain ⟨i, rfl⟩ := hi
      rw [Fin.strictMono_castSucc.injective.extend_apply]
      by_cases hj : ∃ j₀, Fin.castSucc j₀ = j
      · obtain ⟨j, rfl⟩ := hj
        rwa [Fin.strictMono_castSucc.injective.extend_apply, hk.lt_iff_lt,
          ← Fin.castSucc_lt_castSucc_iff]
      · rw [Function.extend_apply' _ _ _ hj]
        apply Polynomial.lt_natDegree_of_mem_eraseLead_support
        rw [mem_support_iff, hf, finset_sum_coeff]
        rw [sum_eq_single, coeff_C_mul, coeff_X_pow_self, mul_one]
        · exact hx i
        · intro j _ hji
          rw [coeff_C_mul, coeff_X_pow, if_neg (hk.injective.ne hji.symm), mul_zero]
        · exact fun hi => (hi (Finset.mem_univ i)).elim
    · intro i
      by_cases hi : ∃ i₀, Fin.castSucc i₀ = i
      · obtain ⟨i, rfl⟩ := hi
        rw [Fin.strictMono_castSucc.injective.extend_apply]
        exact hx i
      · rw [Function.extend_apply' _ _ _ hi, Ne, leadingCoeff_eq_zero, ← card_support_eq_zero, h]
        exact n.succ_ne_zero
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.strictMono_castSucc.injective.extend_apply]
      rw [← hf, Function.extend_apply', Function.extend_apply', Polynomial.eraseLead_add_C_mul_X_pow]
      all_goals exact H

