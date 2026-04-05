import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

variable (x y : ℤ) [K.HasTotal (up ℤ)]

set_option backward.isDefEq.respectTransparency false in
theorem ι_totalShift₁Iso_hom_f (a b n : ℤ) (h : a + b = n) (a' : ℤ) (ha' : a' = a + x)
    (n' : ℤ) (hn' : n' = n + x) :
    ((shiftFunctor₁ C x).obj K).ιTotal (up ℤ) a b n h ≫ (K.totalShift₁Iso x).hom.f n =
      (K.shiftFunctor₁XXIso a x a' ha' b).hom ≫ K.ιTotal (up ℤ) a' b n' (by dsimp; lia) ≫
        (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) x n n' hn').inv := by
  subst ha' hn'
  dsimp [HomologicalComplex₂.totalShift₁Iso, HomologicalComplex₂.totalShift₁XIso]
  simp only [ι_totalDesc, comp_id, id_comp]

