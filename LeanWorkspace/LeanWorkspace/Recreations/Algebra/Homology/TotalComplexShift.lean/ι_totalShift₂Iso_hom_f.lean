import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

variable (x y : ℤ) [K.HasTotal (up ℤ)]

set_option backward.isDefEq.respectTransparency false in
theorem ι_totalShift₂Iso_hom_f (a b n : ℤ) (h : a + b = n) (b' : ℤ) (hb' : b' = b + y)
    (n' : ℤ) (hn' : n' = n + y) :
    ((shiftFunctor₂ C y).obj K).ιTotal (up ℤ) a b n h ≫ (K.totalShift₂Iso y).hom.f n =
      (a * y).negOnePow • (K.shiftFunctor₂XXIso a b y b' hb').hom ≫
        K.ιTotal (up ℤ) a b' n' (by dsimp; lia) ≫
          (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) y n n' hn').inv := by
  subst hb' hn'
  dsimp [HomologicalComplex₂.totalShift₂Iso, HomologicalComplex₂.totalShift₂XIso]
  simp only [ι_totalDesc, comp_id, id_comp]

