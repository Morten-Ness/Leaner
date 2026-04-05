import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {R V : Type*} [CommRing R] [InvolutiveStar R] [AddCommGroup V] [StarAddMonoid V]
  [Module R V] [StarModule R V]

theorem spectrum_intrinsicStar (f : WithConv (Module.End R V)) :
    spectrum R (star f).ofConv = star (spectrum R f.ofConv) := by
  ext x
  simp_rw [Set.mem_star, spectrum.mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one]
  rw [← isUnit_intrinsicStar_iff]
  simp [one_eq_id]

