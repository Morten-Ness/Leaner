import Mathlib

variable {R : Type u} [Ring R] [TopologicalSpace R]

variable {M N : TopModuleCat.{v} R} (φ : M ⟶ N)

theorem cokerπ_surjective : Function.Surjective (TopModuleCat.cokerπ φ).hom := Submodule.mkQ_surjective _

