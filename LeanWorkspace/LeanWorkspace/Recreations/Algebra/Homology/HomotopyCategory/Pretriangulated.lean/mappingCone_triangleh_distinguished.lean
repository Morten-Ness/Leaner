import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasZeroObject C]

theorem mappingCone_triangleh_distinguished {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    CochainComplex.mappingCone.triangleh f ∈ distTriang (HomotopyCategory _ _) := ⟨_, _, f, ⟨Iso.refl _⟩⟩

