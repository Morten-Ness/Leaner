import Mathlib

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

theorem quotient_inverts_homotopyEquivalences :
    (HomologicalComplex.homotopyEquivalences V c).IsInvertedBy (HomotopyCategory.quotient V c) := by
  rintro K L _ ⟨e, rfl⟩
  change IsIso (HomotopyCategory.isoOfHomotopyEquiv e).hom
  infer_instance

