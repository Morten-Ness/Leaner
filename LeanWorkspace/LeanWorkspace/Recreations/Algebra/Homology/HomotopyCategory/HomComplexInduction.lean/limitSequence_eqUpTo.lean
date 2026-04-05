import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ}

variable {d : ℤ} {X : ℕ → Set (Cochain K L d)} (φ : ∀ (n : ℕ), X n → X (n + 1))
   {p₀ : ℤ} (hφ : ∀ (n : ℕ) (x : X n), (φ n x).val.EqUpTo x.val (p₀ + n)) (x₀ : X 0)

theorem limitSequence_eqUpTo (n : ℕ) :
    (CochainComplex.HomComplex.Cochain.InductionUp.limitSequence φ hφ x₀).EqUpTo (CochainComplex.HomComplex.Cochain.InductionUp.sequence φ x₀ n).1 (p₀ + n) := by
  intro p q hpq hp
  exact CochainComplex.HomComplex.Cochain.InductionUp.sequence_eqUpTo φ hφ _ _ _ (by lia) _ _ _ (by lia)

