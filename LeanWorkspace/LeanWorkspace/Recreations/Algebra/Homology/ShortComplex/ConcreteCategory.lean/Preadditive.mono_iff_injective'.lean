import Mathlib

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}

variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC] [HasForget₂ C Ab]

variable [Preadditive C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  (S : ShortComplex C)

variable [HasZeroObject C]

theorem Preadditive.mono_iff_injective' {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f := by
  simp only [mono_iff_injective, ← CategoryTheory.mono_iff_injective]
  apply (MorphismProperty.monomorphisms (Type w)).arrow_mk_iso_iff
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  exact Arrow.isoOfNatIso e (Arrow.mk f)

