import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem map_div {B : Type*} [CommSemiring B] [Algebra R B] (I J : Submodule R A)
    (h : A ≃ₐ[R] B) : (I / J).map h.toLinearMap = I.map h.toLinearMap / J.map h.toLinearMap := by
  ext x
  simp only [mem_map, Submodule.mem_div_iff_forall_mul_mem, AlgEquiv.toLinearMap_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, hx _ hy, Submodule.map_mul h x y⟩
  · rintro hx
    refine ⟨h.symm x, fun z hz => ?_, h.apply_symm_apply x⟩
    obtain ⟨xz, xz_mem, hxz⟩ := hx (h z) ⟨z, hz, rfl⟩
    convert xz_mem
    apply h.injective
    rw [Submodule.map_mul, h.apply_symm_apply, hxz]

