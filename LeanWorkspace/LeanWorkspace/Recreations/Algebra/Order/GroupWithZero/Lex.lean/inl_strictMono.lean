import Mathlib

variable {M₀ N₀ : Type*}

theorem inl_strictMono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [PartialOrder N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] : StrictMono (inl M₀ N₀) := MonoidWithZeroHom.inl_mono.strictMono_of_injective inl_injective

