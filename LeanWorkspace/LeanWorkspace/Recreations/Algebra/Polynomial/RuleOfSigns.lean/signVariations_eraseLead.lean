import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] (P : Polynomial R)

theorem signVariations_eraseLead (h : SignType.sign P.leadingCoeff = SignType.sign P.nextCoeff) :
    Polynomial.signVariations P.eraseLead = Polynomial.signVariations P := by
  by_cases hpz : P = 0
  · simp_all
  · have h₂ : nextCoeff P ≠ 0 := by intro; simp_all
    obtain ⟨_, hl⟩ := coeffList_eq_cons_leadingCoeff (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂)
    simp [Polynomial.signVariations, List.destutter, leadingCoeff_eraseLead_eq_nextCoeff h₂, hl, h, h₂,
      coeffList_eraseLead hpz]

