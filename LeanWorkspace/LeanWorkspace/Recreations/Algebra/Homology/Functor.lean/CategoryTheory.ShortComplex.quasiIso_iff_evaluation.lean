import Mathlib

variable {T : Type*} [Category* T] {V : Type*} [Category* V]

variable [Abelian V] {S₁ S₂ : ShortComplex (T ⥤ V)} (f : S₁ ⟶ S₂)

theorem quasiIso_iff_evaluation :
    QuasiIso f ↔ ∀ (j : T),
      QuasiIso (((evaluation T V).obj j).mapShortComplex.map f) := ⟨fun _ ↦ inferInstance, fun hf ↦ by
    rw [quasiIso_iff, NatTrans.isIso_iff_isIso_app]
    exact fun j ↦ ((MorphismProperty.isomorphisms V).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
      ((homologyFunctorIso ((evaluation T V).obj j)))).app (Arrow.mk f))).1
        ((quasiIso_iff _).1 (hf j))⟩

