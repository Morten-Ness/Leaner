import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

theorem covariant_sequence_exact₃ {n₀ : ℕ} (x₃ : CategoryTheory.Abelian.Ext X S.X₃ n₀) {n₁ : ℕ} (hn₁ : n₀ + 1 = n₁)
    (hx₃ : x₃.comp hS.extClass hn₁ = 0) :
    ∃ (x₂ : CategoryTheory.Abelian.Ext X S.X₂ n₀), x₂.comp (mk₀ S.g) (add_zero n₀) = x₃ := by
  have := CategoryTheory.Abelian.Ext.covariant_sequence_exact₃' X hS n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

