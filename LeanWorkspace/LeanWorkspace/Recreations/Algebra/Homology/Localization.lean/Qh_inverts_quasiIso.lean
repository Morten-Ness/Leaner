import Mathlib

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

variable [(HomologicalComplex.quasiIso C c).HasLocalization] [c.QFactorsThroughHomotopy C]

set_option backward.isDefEq.respectTransparency false in
theorem Qh_inverts_quasiIso : (HomotopyCategory.quasiIso C c).IsInvertedBy HomologicalComplexUpToQuasiIso.Qh := by
  rintro ⟨K⟩ ⟨L⟩ φ
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff φ,
    ← HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso]
  exact (NatIso.isIso_map_iff (HomologicalComplexUpToQuasiIso.quotientCompQhIso C c) φ).2

