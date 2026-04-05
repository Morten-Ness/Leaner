import Mathlib

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC] [HasForget₂ C Ab.{v}]
  [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  {ι : Type*} {c : ComplexShape ι}

variable {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

theorem δ_apply' (x₃ : (forget₂ C Ab).obj (S.X₃.homology i))
    (x₂ : (forget₂ C Ab).obj (S.X₂.opcycles i))
    (x₁ : (forget₂ C Ab).obj (S.X₁.cycles j))
    (h₂ : (forget₂ C Ab).map (HomologicalComplex.opcyclesMap S.g i) x₂ =
      (forget₂ C Ab).map (S.X₃.homologyι i) x₃)
    (h₁ : (forget₂ C Ab).map (HomologicalComplex.cyclesMap S.f j) x₁ =
      (forget₂ C Ab).map (S.X₂.opcyclesToCycles i j) x₂) :
    (forget₂ C Ab).map (hS.δ i j hij) x₃ = (forget₂ C Ab).map (S.X₁.homologyπ j) x₁ := (HomologicalComplex.HomologySequence.snakeInput hS i j hij).δ_apply' x₃ x₂ x₁ h₂ h₁

