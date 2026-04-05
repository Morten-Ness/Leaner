import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem inr_snd :
    (Cochain.ofHom (CochainComplex.mappingCone.inr φ)).comp (CochainComplex.mappingCone.snd φ) (zero_add 0) = Cochain.ofHom (𝟙 G) := by cat_disch

