import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem δ_fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (n' q' : ℤ) (h' : p + n' = q') :
    δ n n' (CochainComplex.HomComplex.Cochain.fromSingleMk f h) = CochainComplex.HomComplex.Cochain.fromSingleMk (f ≫ K.d q q') h' := by
  by_cases hq : q + 1 = q'
  · dsimp only [CochainComplex.HomComplex.Cochain.fromSingleMk]
    rw [δ_single _ n n' (by lia) (p - 1) q' (by lia) hq]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K q q' (by simp; lia),
      CochainComplex.HomComplex.Cochain.fromSingleMk]

