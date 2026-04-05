import Mathlib

open scoped Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}

variable [MonoidWithZero M₀]

theorem map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZero G₀'] [FunLike F G₀ G₀']
    [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n : ℤ) : f (x ^ n) = f x ^ n := map_zpow' f (map_inv₀ f) x n

