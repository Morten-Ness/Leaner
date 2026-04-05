import Mathlib

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}

variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC] [HasForget₂ C Ab]

variable [Preadditive C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  (S : ShortComplex C)

variable [HasZeroObject C]

theorem Preadditive.epi_iff_surjective {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective ((forget₂ C Ab).map f) := by
  rw [← AddCommGrpCat.epi_iff_surjective]
  constructor
  · intro
    infer_instance
  · apply Functor.epi_of_epi_map

