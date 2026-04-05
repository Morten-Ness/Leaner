import Mathlib

variable {n : ℕ} {M M₁ : Type*}

variable {F S : Type*} [AddCommGroup M] [AddCommGroup M₁] [FunLike F M M₁]
  [AddMonoidHomClass F M M₁] [Module (ZMod n) M] [Module (ZMod n) M₁] [SetLike S M]
  [AddSubgroupClass S M] {x : M} {K : S}

theorem toZModLinearMap_injective : Function.Injective <| AddMonoidHom.toZModLinearMap n (M := M) (M₁ := M₁) :=
  fun _ _ h ↦ ext fun x ↦ congr($h x)

