import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

theorem mem_subcategoryAcyclic_iff (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    HomotopyCategory.subcategoryAcyclic C X ↔ ∀ (n : ℤ), IsZero ((homologyFunctor _ _ n).obj X) := Functor.mem_homologicalKernel_iff _ X

