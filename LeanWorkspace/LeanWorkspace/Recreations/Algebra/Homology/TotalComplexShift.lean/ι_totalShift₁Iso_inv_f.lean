import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

variable (x y : ℤ) [K.HasTotal (up ℤ)]

theorem ι_totalShift₁Iso_inv_f (a b n : ℤ) (h : a + b = n) (a' n' : ℤ)
    (ha' : a' + b = n') (hn' : n' = n + x) :
    K.ιTotal (up ℤ) a' b n' ha' ≫
      (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) x n n' hn').inv ≫
        (K.totalShift₁Iso x).inv.f n =
      (K.shiftFunctor₁XXIso a x a' (by lia) b).inv ≫
        ((shiftFunctor₁ C x).obj K).ιTotal (up ℤ) a b n h := by
  subst hn'
  obtain rfl : a = a' - x := by lia
  dsimp [HomologicalComplex₂.totalShift₁Iso, HomologicalComplex₂.totalShift₁XIso, HomologicalComplex₂.shiftFunctor₁XXIso, XXIsoOfEq]
  simp only [id_comp, ι_totalDesc]

