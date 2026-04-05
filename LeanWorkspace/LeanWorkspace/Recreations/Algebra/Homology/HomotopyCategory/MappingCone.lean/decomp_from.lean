import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem decomp_from {j : ℤ} {A : C} (f : (CochainComplex.mappingCone φ).X j ⟶ A) (i : ℤ) (hij : j + 1 = i) :
    ∃ (a : F.X i ⟶ A) (b : G.X j ⟶ A),
      f = (CochainComplex.mappingCone.fst φ).1.v j i hij ≫ a + (CochainComplex.mappingCone.snd φ).v j j (add_zero j) ≫ b := ⟨(CochainComplex.mappingCone.inl φ).v i j (by lia) ≫ f, (CochainComplex.mappingCone.inr φ).f j ≫ f,
    by apply CochainComplex.mappingCone.ext_from φ i j hij <;> simp⟩

