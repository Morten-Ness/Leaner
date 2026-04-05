import Mathlib

variable {T : Type*} [Category* T] {V : Type*} [Category* V]

variable [Abelian V] {ι : Type*} {c : ComplexShape ι} {K₁ K₂ : HomologicalComplex (T ⥤ V) c}
  (f : K₁ ⟶ K₂)

theorem quasiIsoAt_iff_evaluation (i : ι) :
    QuasiIsoAt f i ↔ ∀ (t : T),
      QuasiIsoAt ((((evaluation T V).obj t).mapHomologicalComplex c).map f) i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff_evaluation]
  rfl

