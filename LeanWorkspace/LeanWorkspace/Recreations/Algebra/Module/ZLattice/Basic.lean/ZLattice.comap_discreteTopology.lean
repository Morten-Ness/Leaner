import Mathlib

variable (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)

theorem ZLattice.comap_discreteTopology [hL : DiscreteTopology L] {e : F →ₗ[K] E}
    (he₁ : Continuous e) (he₂ : Function.Injective e) :
    DiscreteTopology (ZLattice.comap K L e) := by
  exact DiscreteTopology.preimage_of_continuous_injective L he₁ he₂

