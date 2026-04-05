import Mathlib

theorem homotopyEquivalences_le_quasiIso
    {ι : Type*} (C : Type u) [Category.{v} C] [Preadditive C]
    (c : ComplexShape ι) [CategoryWithHomology C] :
    homotopyEquivalences C c ≤ HomologicalComplex.quasiIso C c := by
  rintro K L _ ⟨e, rfl⟩
  simp only [HomologicalComplex.mem_quasiIso_iff]
  infer_instance

