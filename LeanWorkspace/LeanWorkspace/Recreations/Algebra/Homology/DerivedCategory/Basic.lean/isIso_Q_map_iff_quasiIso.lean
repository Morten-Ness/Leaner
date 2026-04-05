import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

theorem isIso_Q_map_iff_quasiIso {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (DerivedCategory.Q.map φ) ↔ QuasiIso φ := by
  apply HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso

