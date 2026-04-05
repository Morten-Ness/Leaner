import Mathlib

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}

variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC] [HasForget₂ C Ab]

variable [Preadditive C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  (S : ShortComplex C)

theorem ShortExact.surjective_g [HasZeroObject C] (hS : S.ShortExact) :
    Function.Surjective ((forget₂ C Ab).map S.g) := by
  rw [← CategoryTheory.Preadditive.epi_iff_surjective]
  exact hS.epi_g

