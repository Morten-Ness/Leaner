import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem δ_snd :
    δ 0 1 (CochainComplex.mappingCone.snd φ) = -(CochainComplex.mappingCone.fst φ).1.comp (Cochain.ofHom φ) (add_zero 1) := by
  ext p q hpq
  simp [CochainComplex.mappingCone.d_snd_v φ p q hpq]

