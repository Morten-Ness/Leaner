import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem δ_toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (n' p' : ℤ) (h' : p' + n' = q) :
    δ n n' (CochainComplex.HomComplex.Cochain.toSingleMk f h) = n'.negOnePow • CochainComplex.HomComplex.Cochain.toSingleMk (K.d p' p ≫ f) h' := by
  by_cases hp : p' + 1 = p
  · dsimp only [CochainComplex.HomComplex.Cochain.toSingleMk]
    rw [δ_single _ n n' (by lia) p' (q + 1) (by lia) rfl]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K p' p (by simp; lia)]

