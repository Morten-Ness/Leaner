import Mathlib

variable {ι R S : Type*} [CommRing R] [Ring S] [Algebra R S]

theorem coeff_divModByMonicAux_mem_span_pow_mul_span : ∀ (p q : S[X]) (hq : q.Monic) (i),
    (p.divModByMonicAux hq).1.coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) ∧
    (p.divModByMonicAux hq).2.coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p)
  | p, q, hq, i => by
    rw [divModByMonicAux]
    have H₀ (i) : p.coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by
      refine SetLike.le_def.mp ?_ <| subset_span <| mem_range_self i
      calc
        span R coeffs(p)
        _ = 1 ^ deg(p) * span R coeffs(p) := by simp
        _ ≤ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by gcongr; exacts [le_sup_left, le_sup_right]
    split_ifs with hpq; swap
    · simpa using H₀ _
    simp only [coeff_add, coeff_C_mul, coeff_X_pow]
    generalize hr : (p - q * (C p.leadingCoeff * X ^ (deg(p) - deg(q)))) = r
    by_cases hr' : r = 0
    · simp only [mul_ite, mul_one, mul_zero, hr', divModByMonicAux, degree_zero, le_bot_iff,
        degree_eq_bot, ne_eq, not_true_eq_false, and_false, ↓reduceDIte, coeff_zero, add_zero,
        Submodule.zero_mem, and_true]
      split_ifs
      exacts [H₀ _, zero_mem _]
    have H : span R coeffs(r) ≤ span R coeffs(p) ⊔ span R coeffs(q) * span R coeffs(p) := by
      rw [span_le, ← hr]
      rintro _ ⟨i, rfl⟩
      rw [coeff_sub, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
      apply sub_mem
      · exact SetLike.le_def.mp le_sup_left (subset_span (mem_range_self _))
      · split_ifs
        · refine SetLike.le_def.mp le_sup_right (mul_mem_mul ?_ ?_) <;> exact subset_span ⟨_, rfl⟩
        · exact zero_mem _
    have deg_r_lt_deg_p : deg(r) < deg(p) := natDegree_lt_natDegree hr' (hr ▸ div_wf_lemma hpq hq)
    have H'' := calc
      spanCoeffs(q) ^ deg(r) * spanCoeffs(r)
      _ ≤ spanCoeffs(q) ^ deg(r) *
          (1 ⊔ (span R coeffs(p) ⊔ span R coeffs(q) * span R coeffs(p))) := by gcongr
      _ ≤ spanCoeffs(q) ^ deg(r) * (spanCoeffs(q) * spanCoeffs(p)) := by
        gcongr
        simp only [sup_le_iff]
        refine ⟨one_le_mul le_sup_left le_sup_left, ?_, mul_le_mul' le_sup_right le_sup_right⟩
        rw [Submodule.sup_mul, one_mul]
        exact le_sup_of_le_left le_sup_right
      _ = spanCoeffs(q) ^ (deg(r) + 1) * spanCoeffs(p) := by rw [pow_succ, mul_assoc]
      _ ≤ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by gcongr; exacts [le_sup_left, deg_r_lt_deg_p]
    refine ⟨add_mem ?_ ?_, ?_⟩
    · split_ifs <;> simp only [mul_one, mul_zero]
      exacts [H₀ _, zero_mem _]
    · exact H'' (coeff_divModByMonicAux_mem_span_pow_mul_span r _ hq i).1
    · exact H'' (coeff_divModByMonicAux_mem_span_pow_mul_span _ _ hq i).2
  termination_by p => deg(p)

