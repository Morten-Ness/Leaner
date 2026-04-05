import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem exact_iff_δlast {n : ℕ} (S : CategoryTheory.ComposableArrows C (n + 2)) :
    S.Exact ↔ S.δlast.Exact ∧ (mk₂ (S.map' n (n + 1)) (S.map' (n + 1) (n + 2))).Exact := by
  constructor
  · intro h
    constructor
    · exact Exact.mk (IsComplex.mk (fun i hi => h.toIsComplex.zero i))
        (fun i hi => h.exact i)
    · rw [CategoryTheory.ComposableArrows.exact₂_iff]; swap
      · rw [CategoryTheory.ComposableArrows.isComplex₂_iff]
        exact h.toIsComplex.zero n
      exact h.exact n (by lia)
  · rintro ⟨h, h'⟩
    refine Exact.mk (IsComplex.mk (fun i hi => ?_)) (fun i hi => ?_)
    · simp only [Nat.add_le_add_iff_right] at hi
      obtain hi | rfl := hi.lt_or_eq
      · exact h.toIsComplex.zero i
      · exact h'.toIsComplex.zero 0
    · simp only [Nat.add_le_add_iff_right] at hi
      obtain hi | rfl := hi.lt_or_eq
      · exact h.exact i
      · exact h'.exact 0

