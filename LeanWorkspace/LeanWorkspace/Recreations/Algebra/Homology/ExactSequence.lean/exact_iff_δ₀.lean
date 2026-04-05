import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem exact_iff_δ₀ (S : CategoryTheory.ComposableArrows C (n + 2)) :
    S.Exact ↔ (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact ∧ S.δ₀.Exact := by
  constructor
  · intro h
    constructor
    · rw [CategoryTheory.ComposableArrows.exact₂_iff]; swap
      · rw [CategoryTheory.ComposableArrows.isComplex₂_iff]
        exact h.toIsComplex.zero 0
      exact h.exact 0 (by lia)
    · exact Exact.mk (IsComplex.mk (fun i hi => h.toIsComplex.zero (i + 1)))
        (fun i hi => h.exact (i + 1))
  · rintro ⟨h, h₀⟩
    refine Exact.mk (IsComplex.mk (fun i hi => ?_)) (fun i hi => ?_)
    · obtain _ | i := i
      · exact h.toIsComplex.zero 0
      · exact h₀.toIsComplex.zero i
    · obtain _ | i := i
      · exact h.exact 0
      · exact h₀.exact i

