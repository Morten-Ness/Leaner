FAIL
import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem inl_injective [DecidablePred fun x : G₀ ↦ x = 0] :
    Function.Injective (MonoidWithZeroHom.inl G₀ H₀) := by
  intro a b h
  simpa [MonoidWithZeroHom.inl] using congrArg Prod.fst h
