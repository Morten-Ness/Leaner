import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

theorem AddMonoidHom.toNatLinearMap_injective [AddCommMonoid M] [AddCommMonoid M₂] :
    Function.Injective (@AddMonoidHom.toNatLinearMap M M₂ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

