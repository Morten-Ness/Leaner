import Mathlib

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}

variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC] [HasForget₂ C Ab]

variable [Preadditive C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  (S : ShortComplex C)

theorem exact_iff_exact_map_forget₂ [S.HasHomology] :
    S.Exact ↔ (S.map (forget₂ C Ab)).Exact := (S.exact_map_iff_of_faithful (forget₂ C Ab)).symm

