import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem decomp_to {i : ℤ} {A : C} (f : A ⟶ (CochainComplex.mappingCone φ).X i) (j : ℤ) (hij : i + 1 = j) :
    ∃ (a : A ⟶ F.X j) (b : A ⟶ G.X i), f = a ≫ (CochainComplex.mappingCone.inl φ).v j i (by lia) + b ≫ (CochainComplex.mappingCone.inr φ).f i := ⟨f ≫ (CochainComplex.mappingCone.fst φ).1.v i j hij, f ≫ (CochainComplex.mappingCone.snd φ).v i i (add_zero i),
    by apply CochainComplex.mappingCone.ext_to φ i j hij <;> simp⟩

