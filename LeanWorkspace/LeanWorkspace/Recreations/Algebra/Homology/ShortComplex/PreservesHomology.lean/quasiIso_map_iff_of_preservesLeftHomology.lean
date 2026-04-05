import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

variable (φ) [S₁.HasHomology] [S₂.HasHomology]
    [(F.mapShortComplex.obj S₁).HasHomology] [(F.mapShortComplex.obj S₂).HasHomology]

set_option backward.isDefEq.respectTransparency false in
theorem quasiIso_map_iff_of_preservesLeftHomology
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂]
    [F.ReflectsIsomorphisms] :
    QuasiIso (F.mapShortComplex.map φ) ↔ QuasiIso φ := by
  have γ : LeftHomologyMapData φ S₁.leftHomologyData S₂.leftHomologyData := default
  rw [γ.quasiIso_iff, (γ.map F).quasiIso_iff, LeftHomologyMapData.map_φH]
  constructor
  · intro
    exact isIso_of_reflects_iso _ F
  · intro
    infer_instance

