import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

variable (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

theorem covariantSequence_exact :
    (CategoryTheory.Abelian.Ext.covariantSequence X hS n₀ n₁ h).Exact := exact_of_δ₀ (CategoryTheory.Abelian.Ext.covariant_sequence_exact₂' X hS n₀).exact_toComposableArrows
    (exact_of_δ₀ (CategoryTheory.Abelian.Ext.covariant_sequence_exact₃' X hS n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (CategoryTheory.Abelian.Ext.covariant_sequence_exact₁' X hS n₀ n₁ h).exact_toComposableArrows
        (CategoryTheory.Abelian.Ext.covariant_sequence_exact₂' X hS n₁).exact_toComposableArrows))

