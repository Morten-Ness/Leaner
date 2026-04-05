import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

variable (x y : ℤ) [K.HasTotal (up ℤ)]

theorem ι_totalShift₂Iso_inv_f (a b n : ℤ) (h : a + b = n) (b' n' : ℤ)
    (hb' : a + b' = n') (hn' : n' = n + y) :
    K.ιTotal (up ℤ) a b' n' hb' ≫
      (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) y n n' hn').inv ≫
        (K.totalShift₂Iso y).inv.f n =
      (a * y).negOnePow • (K.shiftFunctor₂XXIso a b y b' (by lia)).inv ≫
        ((shiftFunctor₂ C y).obj K).ιTotal (up ℤ) a b n h := by
  subst hn'
  obtain rfl : b = b' - y := by lia
  dsimp [HomologicalComplex₂.totalShift₂Iso, HomologicalComplex₂.totalShift₂XIso, HomologicalComplex₂.shiftFunctor₂XXIso, XXIsoOfEq]
  simp only [id_comp, ι_totalDesc]

