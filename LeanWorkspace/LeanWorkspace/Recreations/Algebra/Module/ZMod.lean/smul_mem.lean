import Mathlib

variable {n : ℕ} {M M₁ : Type*}

variable {F S : Type*} [AddCommGroup M] [AddCommGroup M₁] [FunLike F M M₁]
  [AddMonoidHomClass F M M₁] [Module (ZMod n) M] [Module (ZMod n) M₁] [SetLike S M]
  [AddSubgroupClass S M] {x : M} {K : S}

theorem smul_mem (hx : x ∈ K) (c : ZMod n) : c • x ∈ K := by
  rw [← ZMod.intCast_zmod_cast c, Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx (cast c)

