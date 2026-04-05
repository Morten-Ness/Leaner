import Mathlib

variable {T : Type*} [Category* T] {V : Type*} [Category* V]

variable [Abelian V] {ι : Type*} {c : ComplexShape ι} {K₁ K₂ : HomologicalComplex (T ⥤ V) c}
  (f : K₁ ⟶ K₂)

theorem quasiIso_iff_evaluation :
    QuasiIso f ↔ ∀ (t : T),
      QuasiIso ((((evaluation T V).obj t).mapHomologicalComplex c).map f) := by
  simp only [quasiIso_iff, HomologicalComplex.quasiIsoAt_iff_evaluation]
  tauto

