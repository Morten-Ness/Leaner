import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem toSingleMk_precomp
    {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0)
    {L : CochainComplex C ℤ} (g : L ⟶ K) :
    CochainComplex.HomComplex.Cocycle.toSingleMk (g.f p ≫ f) h p' hp' (by simp [← g.comm_assoc, hf]) =
      (CochainComplex.HomComplex.Cocycle.toSingleMk f h p' hp' hf).precomp g := by
  ext : 1
  exact (Cochain.toSingleEquiv h).injective (by simp [Cochain.toSingleMk_precomp])

