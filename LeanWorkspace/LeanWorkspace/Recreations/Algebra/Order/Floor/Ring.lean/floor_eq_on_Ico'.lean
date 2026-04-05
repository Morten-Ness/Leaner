import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem floor_eq_on_Ico' (n : ℤ) : ∀ a ∈ Set.Ico (n : R) (n + 1), (⌊a⌋ : R) = n := fun a ha =>
  congr_arg _ <| Int.floor_eq_on_Ico n a ha

