import Mathlib

variable {n : ℕ} {M M₁ : Type*}

variable {F S : Type*} [AddCommGroup M] [AddCommGroup M₁] [FunLike F M M₁]
  [AddMonoidHomClass F M M₁] [Module (ZMod n) M] [Module (ZMod n) M₁] [SetLike S M]
  [AddSubgroupClass S M] {x : M} {K : S}

theorem coe_toZModLinearMap (f : M →+ M₁) : ⇑(f.toZModLinearMap n) = f := rfl

