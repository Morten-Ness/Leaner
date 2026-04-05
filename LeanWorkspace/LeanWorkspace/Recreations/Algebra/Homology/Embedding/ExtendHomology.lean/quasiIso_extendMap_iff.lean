import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem quasiIso_extendMap_iff [∀ j, K.HasHomology j] [∀ j, L.HasHomology j] :
    QuasiIso (extendMap φ e) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, ← fun j ↦ HomologicalComplex.quasiIsoAt_extendMap_iff φ e (j := j) (hj' := rfl)]
  constructor
  · tauto
  · intro h j'
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      exact h j
    · rw [quasiIsoAt_iff_exactAt]
      all_goals
        exact HomologicalComplex.extend_exactAt _ _ _ (by simpa using hj')

