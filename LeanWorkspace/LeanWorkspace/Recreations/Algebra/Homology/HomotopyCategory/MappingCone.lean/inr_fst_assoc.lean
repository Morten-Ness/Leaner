import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem inr_fst_assoc {K : CochainComplex C ℤ} {d e f : ℤ} (γ : Cochain F K d)
    (he : 1 + d = e) (hf : 0 + e = f) :
    (Cochain.ofHom (CochainComplex.mappingCone.inr φ)).comp ((CochainComplex.mappingCone.fst φ).1.comp γ he) hf = 0 := by
  obtain rfl : e = f := by lia
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, CochainComplex.mappingCone.inr_fst, Cochain.zero_comp]

