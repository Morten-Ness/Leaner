import Mathlib

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC] [HasForget₂ C Ab.{v}]
  [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  {ι : Type*} {c : ComplexShape ι}

variable {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

include hS in
theorem d_eq_zero_of_f_eq_d_apply
    (x₂ : ((forget₂ C Ab).obj (S.X₂.X i))) (x₁ : ((forget₂ C Ab).obj (S.X₁.X j)))
    (hx₁ : ((forget₂ C Ab).map (S.f.f j)) x₁ = ((forget₂ C Ab).map (S.X₂.d i j)) x₂) (k : ι) :
    ((forget₂ C Ab).map (S.X₁.d j k)) x₁ = 0 := by
  have := hS.mono_f
  apply (Preadditive.mono_iff_injective (S.f.f k)).1 inferInstance
  rw [← ConcreteCategory.forget₂_comp_apply, ← HomologicalComplex.Hom.comm,
    ConcreteCategory.forget₂_comp_apply, hx₁, ← ConcreteCategory.forget₂_comp_apply,
    HomologicalComplex.d_comp_d, Functor.map_zero, map_zero]
  rfl

