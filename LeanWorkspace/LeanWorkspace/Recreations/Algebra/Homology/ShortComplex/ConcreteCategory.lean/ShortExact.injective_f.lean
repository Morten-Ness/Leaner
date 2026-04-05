import Mathlib

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}

variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC] [HasForget₂ C Ab]

variable [Preadditive C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  (S : ShortComplex C)

theorem ShortExact.injective_f [HasZeroObject C] (hS : S.ShortExact) :
    Function.Injective ((forget₂ C Ab).map S.f) := by
  rw [← CategoryTheory.Preadditive.mono_iff_injective]
  exact hS.mono_f

