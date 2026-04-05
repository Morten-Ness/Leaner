import Mathlib

open scoped Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] [GroupWithZero G₀'] [FunLike F G₀ G₀']
  [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (a b : G₀)

theorem map_div₀ : f (a / b) = f a / f b := map_div' f (map_inv₀ f) a b

