import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

theorem span_orbit_mem_invtSubmodule {G : Type*}
    [Monoid G] [DistribMulAction G M] [SMulCommClass G R M] (x : M) (g : G) :
    span R (MulAction.orbit G x) ∈ Module.End.invtSubmodule (DistribSMul.toLinearMap R M g) := by
  rw [Module.End.mem_invtSubmodule, Submodule.span_le, Submodule.comap_coe]
  intro y hy
  simp only [Set.mem_preimage, DistribSMul.toLinearMap_apply, SetLike.mem_coe]
  exact Submodule.subset_span <| MulAction.mem_orbit_of_mem_orbit g hy

