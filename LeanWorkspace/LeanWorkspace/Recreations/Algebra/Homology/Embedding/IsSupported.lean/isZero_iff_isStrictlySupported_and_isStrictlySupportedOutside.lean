import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (φ : K ⟶ L) (e : c.Embedding c')

theorem isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside :
    IsZero K ↔ K.IsStrictlySupported e ∧ K.IsStrictlySupportedOutside e := by
  constructor
  · intro hK
    constructor
    all_goals
      constructor
      intros
      exact (eval _ _ _).map_isZero hK
  · rintro ⟨h₁, h₂⟩
    rw [IsZero.iff_id_eq_zero]
    ext n
    apply IsZero.eq_of_src
    by_cases hn : ∃ i, e.f i = n
    · obtain ⟨i, rfl⟩ := hn
      exact h₂.isZero i
    · exact K.isZero_X_of_isStrictlySupported e _ (by simpa using hn)

