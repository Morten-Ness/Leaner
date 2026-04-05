import Mathlib

variable (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)

theorem ofZLatticeComap_repr_apply (e : F ≃ₗ[K] E) {ι : Type*} (b : Module.Basis ι ℤ L) (x : L) (i : ι) :
    (b.ofZLatticeComap K L e).repr (ZLattice.comap_equiv K L e x) i = b.repr x i := by
  simp [Module.Basis.ofZLatticeComap]

