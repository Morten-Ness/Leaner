import Mathlib

variable {R : Type u} [Ring R] [TopologicalSpace R]

variable {M N : TopModuleCat.{v} R} (φ : M ⟶ N)

theorem hom_cokerπ (x) : (TopModuleCat.cokerπ φ).hom x = Submodule.mkQ _ x := rfl

