import Mathlib

open scoped Function in -- required for scoped `on` notation Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

variable [IsDomain R] {p q : R[X]}

theorem exists_multiset_roots [DecidableEq R] :
    ∀ {p : R[X]} (_ : p ≠ 0), ∃ s : Multiset R,
      (Multiset.card s : WithBot ℕ) ≤ degree p ∧ ∀ a, s.count a = rootMultiplicity a p
  | p, hp =>
    haveI := Classical.propDecidable (∃ x, IsRoot p x)
    if h : ∃ x, IsRoot p x then
      let ⟨x, hx⟩ := h
      have hpd : 0 < degree p := degree_pos_of_root hp hx
      have hd0 : p /ₘ (Polynomial.X - Polynomial.C x) ≠ 0 := fun h => by
        rw [← mul_divByMonic_eq_iff_isRoot.2 hx, h, mul_zero] at hp; exact hp rfl
      have wf : degree (p /ₘ (Polynomial.X - Polynomial.C x)) < degree p :=
        degree_divByMonic_lt _ _ hp ((degree_X_sub_C x).symm ▸ by decide)
      let ⟨t, htd, htr⟩ := @exists_multiset_roots _ (p /ₘ (Polynomial.X - Polynomial.C x)) hd0
      have hdeg : degree (Polynomial.X - Polynomial.C x) ≤ degree p := by
        simpa using Nat.WithBot.one_le_iff_zero_lt.mpr hpd
      have hdiv0 : p /ₘ (Polynomial.X - Polynomial.C x) ≠ 0 :=
        mt (divByMonic_eq_zero_iff (Polynomial.monic_X_sub_C x)).1 <| not_lt.2 hdeg
      ⟨x ::ₘ t,
        calc
          (card (x ::ₘ t) : WithBot ℕ) = Multiset.card t + 1 := by
            congr
            exact mod_cast Multiset.card_cons _ _
          _ ≤ degree p := by
            rw [← degree_add_divByMonic (Polynomial.monic_X_sub_C x) hdeg, degree_X_sub_C, add_comm]
            exact add_le_add (le_refl (1 : WithBot ℕ)) htd,
        by
          intro a
          conv_rhs => rw [← mul_divByMonic_eq_iff_isRoot.mpr hx]
          rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero x) hdiv0),
            Polynomial.rootMultiplicity_X_sub_C, ← htr a]
          split_ifs with ha
          · rw [ha, count_cons_self, add_comm]
          · rw [count_cons_of_ne ha, zero_add]⟩
    else
      ⟨0, (degree_eq_natDegree hp).symm ▸ WithBot.coe_le_coe.2 (Nat.zero_le _), by
        intro a
        rw [count_zero, rootMultiplicity_eq_zero (not_exists.mp h a)]⟩
termination_by p => natDegree p
decreasing_by {
  apply (Nat.cast_lt (α := WithBot ℕ)).mp
  simp only [degree_eq_natDegree hp, degree_eq_natDegree hd0] at wf
  assumption}

