import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem d_snd_v' (n : ℤ) :
    (CochainComplex.mappingCone φ).d (n - 1) n ≫ (CochainComplex.mappingCone.snd φ).v n n (add_zero n) =
    (CochainComplex.mappingCone.fst φ : Cochain (CochainComplex.mappingCone φ) F 1).v (n - 1) n (by lia) ≫ φ.f n +
      (CochainComplex.mappingCone.snd φ).v (n - 1) (n - 1) (add_zero _) ≫ G.d (n - 1) n := by
  apply CochainComplex.mappingCone.d_snd_v

