import Mathlib

open scoped Pointwise Ring

variable {F R A : Type*} [CommRing R] [Ring A] [Algebra R A]

variable [FunLike F A R] [AlgHomClass F R A R]

theorem apply_mem_spectrum [Nontrivial R] (φ : F) (a : A) : φ a ∈ σ a := by
  have h : ↑ₐ (φ a) - a ∈ RingHom.ker (φ : A →+* R) := by
    simp only [RingHom.mem_ker, map_sub, RingHom.coe_coe, AlgHomClass.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  simp only [spectrum.mem_iff spectrum, ← mem_nonunits_iff,
    coe_subset_nonunits (RingHom.ker_ne_top (φ : A →+* R)) h]

