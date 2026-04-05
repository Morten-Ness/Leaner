import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ}

variable {d : ℤ} {X : ℕ → Set (Cochain K L d)} (φ : ∀ (n : ℕ), X n → X (n + 1))
   {p₀ : ℤ} (hφ : ∀ (n : ℕ) (x : X n), (φ n x).val.EqUpTo x.val (p₀ + n)) (x₀ : X 0)

include hφ in
theorem sequence_eqUpTo (n₁ n₂ : ℕ) (h : n₁ ≤ n₂) :
    (CochainComplex.HomComplex.Cochain.InductionUp.sequence φ x₀ n₁).val.EqUpTo (CochainComplex.HomComplex.Cochain.InductionUp.sequence φ x₀ n₂).val (p₀ + n₁) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k generalizing n₁ with
  | zero => intro _ _ _ _; simp
  | succ k hk =>
    intro p q hpq hp
    rw [hk n₁ p q hpq hp, ← hφ (n₁ + k) (CochainComplex.HomComplex.Cochain.InductionUp.sequence φ x₀ (n₁ + k)) p q hpq (by lia)]
    dsimp [CochainComplex.HomComplex.Cochain.InductionUp.sequence]

