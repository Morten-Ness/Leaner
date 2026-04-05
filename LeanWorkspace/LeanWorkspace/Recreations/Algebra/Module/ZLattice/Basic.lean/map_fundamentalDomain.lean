import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

theorem map_fundamentalDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] (f : E ≃ₗ[K] F) :
    f '' (ZSpan.fundamentalDomain b) = ZSpan.fundamentalDomain (ZSpan.map b f) := by
  ext x
  rw [ZSpan.mem_fundamentalDomain, Module.Basis.map_repr, LinearEquiv.trans_apply, ← ZSpan.mem_fundamentalDomain,
    show f.symm x = f.toEquiv.symm x by rfl, ← Set.mem_image_equiv]
  rfl

