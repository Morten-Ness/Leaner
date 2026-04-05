import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

theorem AddMonoidHom.toIntLinearMap_injective [AddCommGroup M] [AddCommGroup M₂] :
    Function.Injective (@AddMonoidHom.toIntLinearMap M M₂ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

