import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

variable (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁)

theorem contravariantSequence_exact :
    (CategoryTheory.Abelian.Ext.contravariantSequence hS Y n₀ n₁ h).Exact := exact_of_δ₀ (CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂' hS Y n₀).exact_toComposableArrows
    (exact_of_δ₀ (CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁' hS Y n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃' hS Y n₀ n₁ h).exact_toComposableArrows
        (CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂' hS Y n₁).exact_toComposableArrows))

