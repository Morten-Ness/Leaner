import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] (P : Polynomial R)

theorem signVariations_eq_eraseLead_add_ite {P : Polynomial R} (h : P ≠ 0) :
    Polynomial.signVariations P = Polynomial.signVariations P.eraseLead + if SignType.sign P.leadingCoeff
      = -SignType.sign P.eraseLead.leadingCoeff then 1 else 0 := by
  by_cases hpz : P = 0
  · simp_all
  have hsl : SignType.sign (leadingCoeff P) ≠ 0 := by simp_all
  rw [Polynomial.signVariations, Polynomial.signVariations, coeffList_eraseLead hpz]
  rw [List.map_cons, List.map_append, List.map_replicate]
  rcases h_eL : P.eraseLead.coeffList with _ | ⟨c, cs⟩
  · simp [coeffList_eq_nil.mp h_eL, h]
  simp only [List.filter_append, List.filter_replicate, List.map_cons, List.filter, ne_eq, hsl]
  have h₁ : SignType.sign c ≠ 0 := by
    by_contra h₂
    suffices eraseLead P = 0 by grind [coeffList_zero]
    by_contra h
    have := coeffList_eq_cons_leadingCoeff h
    grind [leadingCoeff_eq_zero, sign_eq_zero_iff]
  simp only [decide_not, sign_zero, List.destutter, Bool.false_eq_true, reduceIte, h₁,
    decide_false, Bool.not_false, List.nil_append, List.destutter', decide_true, Bool.not_true]
  obtain rfl : c = leadingCoeff P.eraseLead := by
    have h_eL : eraseLead P ≠ 0 := by simp [← coeffList_eq_nil, h_eL]
    obtain ⟨ls, hls⟩ := coeffList_eq_cons_leadingCoeff h_eL
    grind
  by_cases h₄ : SignType.sign P.leadingCoeff = SignType.sign P.eraseLead.leadingCoeff
  · grind [SignType.neg_eq_self_iff]
  rw [if_pos h₄, if_pos ?_]
  · grind [Nat.sub_add_cancel, List.length_pos_of_ne_nil, List.destutter'_ne_nil]
  cases _ : SignType.sign P.leadingCoeff
  <;> cases _ : SignType.sign P.eraseLead.leadingCoeff
  <;> grind [= SignType.neg_eq_neg_one, SignType.zero_eq_zero, SignType.pos_eq_one,
      SignType.neg_eq_neg_one, neg_neg]

