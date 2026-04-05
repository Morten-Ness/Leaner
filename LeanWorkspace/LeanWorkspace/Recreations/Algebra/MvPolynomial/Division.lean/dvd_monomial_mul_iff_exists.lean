import Mathlib

variable {σ R : Type*} [CommSemiring R]

variable {R : Type*} [CommRing R] {i : σ} {p q r : MvPolynomial σ R}

theorem dvd_monomial_mul_iff_exists [IsCancelMulZero R] {n : σ →₀ ℕ} :
    p ∣ monomial n 1 * q ↔ ∃ m r, m ≤ n ∧ r ∣ q ∧ p = monomial m 1 * r := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp only [Subsingleton.elim _ p, dvd_refl, and_self, and_true, exists_const, true_iff]
    refine ⟨n, le_refl n⟩
  suffices ∀ (d) (n : σ →₀ ℕ) (hd : n.degree = d) (p q : MvPolynomial σ R),
    p ∣ monomial n 1 * q ↔ ∃ m r, m ≤ n ∧ r ∣ q ∧ p = monomial m 1 * r from this n.degree n rfl p q
  classical
  intro d
  induction d with
  | zero =>
    intro n hn p
    rw [Finsupp.degree_eq_zero_iff] at hn
    simp only [hn, monomial_zero', C_1, one_mul, nonpos_iff_eq_zero, exists_and_left,
      exists_eq_left, exists_eq_right', implies_true]
  | succ d hd =>
    intro n hn p q
    refine ⟨fun hp ↦ ?_, fun ⟨m, r, hmn, hrq, hp⟩ ↦ ?_⟩
    · obtain ⟨i, hi⟩ : n.support.Nonempty := by
        rw [Finsupp.support_nonempty_iff]
        intro hn'
        simp [hn'] at hn
      let n' := n - Finsupp.single i 1
      have hn' : n' + Finsupp.single i 1 = n := by
        apply Finsupp.sub_add_single_one_cancel
        rwa [← Finsupp.mem_support_iff]
      have hnn' : n' ≤ n := by simp [← hn']
      have hd' : n'.degree = d := by
        rw [← add_left_inj, ← hn, ← hn']
        simp
      rw [← hn', monomial_add_single, pow_one, mul_comm _ (X i), mul_assoc, MvPolynomial.dvd_X_mul_iff] at hp
      rcases hp with hp | hp
      · obtain ⟨m, r, hm, hr, hp⟩ := (hd n' hd' p q).mp hp
        exact ⟨m, r, le_trans hm hnn', hr, hp⟩
      · obtain ⟨p', rfl⟩ := hp.1
        obtain ⟨m, r, hm, hr, hp⟩ := (hd n' hd' _ _).mp hp.2
        use m + Finsupp.single i 1, r, ?_, hr
        · simp [monomial_add_single, pow_one, mul_comm _ (X i), mul_assoc, ← hp]
        · simpa [← hn'] using hm
    · rw [hp, ← add_tsub_cancel_of_le hmn, ← mul_one 1, ← monomial_mul, mul_one, mul_assoc]
      apply mul_dvd_mul dvd_rfl
      apply dvd_mul_of_dvd_right hrq

