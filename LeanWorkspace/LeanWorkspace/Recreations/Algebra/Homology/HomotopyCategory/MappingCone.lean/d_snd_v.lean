import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem d_snd_v (i j : ℤ) (hij : i + 1 = j) :
    (CochainComplex.mappingCone φ).d i j ≫ (CochainComplex.mappingCone.snd φ).v j j (add_zero _) =
      (CochainComplex.mappingCone.fst φ).1.v i j hij ≫ φ.f j + (CochainComplex.mappingCone.snd φ).v i i (add_zero i) ≫ G.d i j := by
  dsimp [CochainComplex.mappingCone, CochainComplex.mappingCone.snd, CochainComplex.mappingCone.fst]
  simp only [Cochain.ofHoms_v]
  apply homotopyCofiber.d_sndX

