import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

theorem quasiIso_τ₃ (h₁ : QuasiIso φ.τ₁) (h₂ : QuasiIso φ.τ₂) :
    QuasiIso φ.τ₃ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ hS₁ hS₂
  all_goals infer_instance

