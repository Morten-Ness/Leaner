import Mathlib

open scoped Nat

variable {R S : Type*}

variable [CommSemiring R] {A : Type*} [CommRing A] [Algebra R A]

theorem aeval_sumIDeriv (p : R[X]) (q : ℕ) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - q ∧
      ∀ (r : A), (X - C r) ^ q ∣ p.map (algebraMap R A) →
        aeval r (Polynomial.sumIDeriv p) = q ! • aeval r gp := by
  have h (k) :
      ∃ gp : R[X], gp.natDegree ≤ p.natDegree - q ∧
        ∀ (r : A), (X - C r) ^ q ∣ p.map (algebraMap R A) →
          aeval r (derivative^[k] p) = q ! • aeval r gp := by
    cases lt_or_ge k q with
    | inl hk =>
      use 0
      rw [natDegree_zero]
      use Nat.zero_le _
      intro r ⟨p', hp⟩
      rw [map_zero, smul_zero, Polynomial.aeval_iterate_derivative_of_lt p q r hp hk]
    | inr hk =>
      obtain ⟨gp, gp_le, h⟩ := Polynomial.aeval_iterate_derivative_of_ge A p q hk
      exact ⟨gp, gp_le.trans (tsub_le_tsub_left hk _), fun r _ => h r⟩
  choose c h using h
  choose c_le hc using h
  refine ⟨(range (p.natDegree + 1)).sum c, ?_, ?_⟩
  · refine (natDegree_sum_le _ _).trans ?_
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i _ => c_le i⟩
  intro r ⟨p', hp⟩
  rw [Polynomial.sumIDeriv_apply, map_sum]; simp_rw [hc _ r ⟨_, hp⟩, map_sum, smul_sum]

