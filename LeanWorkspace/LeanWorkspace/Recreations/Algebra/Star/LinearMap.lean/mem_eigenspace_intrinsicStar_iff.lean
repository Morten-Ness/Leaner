import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {R V : Type*} [CommRing R] [InvolutiveStar R] [AddCommGroup V] [StarAddMonoid V]
  [Module R V] [StarModule R V]

theorem mem_eigenspace_intrinsicStar_iff (f : WithConv (Module.End R V)) (α : R) (x : V) :
    x ∈ (star f).ofConv.eigenspace α ↔ star x ∈ f.ofConv.eigenspace (star α) := by
  simp_rw [mem_eigenspace_iff, intrinsicStar_apply, star_eq_iff_star_eq, star_smul, eq_comm]

