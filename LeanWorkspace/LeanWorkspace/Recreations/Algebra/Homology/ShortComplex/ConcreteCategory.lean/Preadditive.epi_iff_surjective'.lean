import Mathlib

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}

variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC] [HasForget₂ C Ab]

variable [Preadditive C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  (S : ShortComplex C)

variable [HasZeroObject C]

theorem Preadditive.epi_iff_surjective' {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  simp only [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective]
  apply (MorphismProperty.epimorphisms (Type w)).arrow_mk_iso_iff
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  exact Arrow.isoOfNatIso e (Arrow.mk f)

