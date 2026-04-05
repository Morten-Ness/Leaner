import Mathlib

variable {R : Type*}

variable [Semiring R]

variable {P : R[X]}

theorem coeffList_eraseLead (h : P ≠ 0) :
    P.coeffList =
      P.leadingCoeff :: (.replicate (P.natDegree - P.eraseLead.degree.succ) 0
        ++ P.eraseLead.coeffList) := by
  by_cases hdp : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdp] at h ⊢
    simp [Polynomial.coeffList_C (C_ne_zero.mp h)]
  by_cases hep : P.eraseLead = 0
  · have h₂ : .monomial P.natDegree P.leadingCoeff = P := by
      simpa [hep] using P.eraseLead_add_monomial_natDegree_leadingCoeff
    nth_rewrite 1 [← h₂]
    simp [Polynomial.coeffList_monomial (Polynomial.leadingCoeff_ne_zero.mpr h), hep]
  have h₁ := withBotSucc_degree_eq_natDegree_add_one h
  have h₂ := withBotSucc_degree_eq_natDegree_add_one hep
  obtain ⟨n, hn, hn2⟩ : ∃ d, P.natDegree = P.eraseLead.natDegree + 1 + d ∧
      d = P.natDegree - P.eraseLead.degree.succ := by
    use P.natDegree - P.eraseLead.natDegree - 1
    have := eraseLead_natDegree_le P
    lia
  rw [← hn2]; clear hn2
  apply List.ext_getElem?
  rintro (_ | k)
  · obtain ⟨w, h⟩ := (Polynomial.coeffList_eq_cons_leadingCoeff h)
    simp_all
  simp only [Polynomial.coeffList, List.map_reverse]
  by_cases! hkd : P.natDegree + 1 ≤ k + 1
  · rw [List.getElem?_eq_none]
      <;> simp <;> lia
  obtain ⟨dk, hdk⟩ := exists_add_of_le (Nat.le_of_lt_succ hkd)
  rw [List.getElem?_reverse (by simpa [withBotSucc_degree_eq_natDegree_add_one h] using hkd),
    List.getElem?_cons_succ, List.length_map, List.length_range, List.getElem?_map,
    List.getElem?_range (by lia), Option.map_some]
  conv_lhs => arg 1; equals P.eraseLead.coeff dk =>
    rw [eraseLead_coeff_of_ne (f := P) dk (by lia)]
    congr
    lia
  by_cases! hkn : k < n
  · simpa [List.getElem?_append, hkn] using coeff_eq_zero_of_natDegree_lt (by lia)
  · rw [List.getElem?_append_right (List.length_replicate ▸ hkn),
      List.length_replicate, List.getElem?_reverse, List.getElem?_map]
    · rw [List.length_map, List.length_range,
        List.getElem?_range (by lia), Option.map_some]
      congr 2
      lia
    · simp
      lia

