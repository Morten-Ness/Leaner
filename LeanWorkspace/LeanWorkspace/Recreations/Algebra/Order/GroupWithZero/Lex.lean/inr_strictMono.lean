import Mathlib

variable {M₀ N₀ : Type*}

theorem inr_strictMono [GroupWithZero M₀] [PartialOrder M₀] [LinearOrderedCommGroupWithZero N₀]
    [DecidablePred fun x : N₀ ↦ x = 0] : StrictMono (inr M₀ N₀) := MonoidWithZeroHom.inr_mono.strictMono_of_injective inr_injective

