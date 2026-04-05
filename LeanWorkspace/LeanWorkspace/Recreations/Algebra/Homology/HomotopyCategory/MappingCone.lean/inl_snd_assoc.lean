import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem inl_snd_assoc {K : CochainComplex C ℤ} {d e f : ℤ} (γ : Cochain G K d)
    (he : 0 + d = e) (hf : -1 + e = f) :
    (CochainComplex.mappingCone.inl φ).comp ((CochainComplex.mappingCone.snd φ).comp γ he) hf = 0 := by
  obtain rfl : e = d := by lia
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain, CochainComplex.mappingCone.inl_snd, Cochain.zero_comp]

