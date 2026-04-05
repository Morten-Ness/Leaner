import Mathlib

variable (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)

theorem ofZLatticeComap_apply (e : F ≃ₗ[K] E) {ι : Type*} (b : Module.Basis ι ℤ L) (i : ι) :
    b.ofZLatticeComap K L e i = e.symm (b i) := by simp [Module.Basis.ofZLatticeComap]

