import Mathlib

variable (R : Type u) [Ring R] [TopologicalSpace R]

variable {S : Type*} [CommRing S] [TopologicalSpace S]

theorem hom_smul {M₁ M₂ : TopModuleCat S} (s : S) (φ : M₁ ⟶ M₂) : (s • φ).hom = s • φ.hom := rfl

