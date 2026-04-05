import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

theorem quasiIso_iff_of_arrow_mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ') :
    QuasiIso φ ↔ QuasiIso φ' := ⟨fun _ => CategoryTheory.ShortComplex.quasiIso_of_arrow_mk_iso φ φ' e, fun _ => CategoryTheory.ShortComplex.quasiIso_of_arrow_mk_iso φ' φ e.symm⟩

