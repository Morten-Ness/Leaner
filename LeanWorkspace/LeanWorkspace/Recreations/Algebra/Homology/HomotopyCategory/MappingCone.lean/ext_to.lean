import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem ext_to (i j : ℤ) (hij : i + 1 = j) {A : C} {f g : A ⟶ (CochainComplex.mappingCone φ).X i}
    (h₁ : f ≫ (CochainComplex.mappingCone.fst φ).1.v i j hij = g ≫ (CochainComplex.mappingCone.fst φ).1.v i j hij)
    (h₂ : f ≫ (CochainComplex.mappingCone.snd φ).v i i (add_zero i) = g ≫ (CochainComplex.mappingCone.snd φ).v i i (add_zero i)) :
    f = g := homotopyCofiber.ext_to_X φ i j hij h₁ (by simpa [CochainComplex.mappingCone.snd] using h₂)

