import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

variable (x y : ℤ) [K.HasTotal (up ℤ)]

theorem totalShift₁Iso_hom_totalShift₂Iso_hom :
    (((shiftFunctor₂ C y).obj K).totalShift₁Iso x).hom ≫ (K.totalShift₂Iso y).hom⟦x⟧' =
      (x * y).negOnePow • (total.map ((HomologicalComplex₂.shiftFunctor₁₂CommIso C x y).hom.app K) (up ℤ) ≫
          (((shiftFunctor₁ C x).obj K).totalShift₂Iso y).hom ≫
          (K.totalShift₁Iso x).hom⟦y⟧' ≫
          (shiftFunctorComm (CochainComplex C ℤ) x y).hom.app _) := congr_arg Iso.hom (HomologicalComplex₂.totalShift₁Iso_trans_totalShift₂Iso K x y)

