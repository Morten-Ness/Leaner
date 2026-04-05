import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem inr_snd_assoc {K : CochainComplex C ℤ} {d e : ℤ} (γ : Cochain G K d) (he : 0 + d = e) :
    (Cochain.ofHom (CochainComplex.mappingCone.inr φ)).comp ((CochainComplex.mappingCone.snd φ).comp γ he) (by simp only [← he, zero_add]) = γ := by
  obtain rfl : d = e := by lia
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, CochainComplex.mappingCone.inr_snd, Cochain.id_comp]

