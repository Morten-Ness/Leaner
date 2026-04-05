import Mathlib

variable {k : Type u} [Field k]

variable {A : Type w} [Ring A] [Algebra k A]

theorem isScalarTower_of_algebra_moduleCat (M : ModuleCat.{v} A) : IsScalarTower k A M := IsScalarTower.restrictScalars k A M

attribute [scoped instance] ModuleCat.isScalarTower_of_algebra_moduleCat

-- We verify that the morphism spaces become `k`-modules.
example (M N : ModuleCat.{v} A) : Module k (M ⟶ N) := inferInstance

