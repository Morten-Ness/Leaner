import Mathlib

variable {C : Type*} [Category.{v} C] [Preadditive C]

variable (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (eval C _ n)).Splitting)

theorem homOfDegreewiseSplit_f (n : ℤ) :
    (CochainComplex.homOfDegreewiseSplit S σ).f n =
      (CochainComplex.cocycleOfDegreewiseSplit S σ).1.v n (n + 1) rfl := by
  simp [CochainComplex.homOfDegreewiseSplit, Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl]

