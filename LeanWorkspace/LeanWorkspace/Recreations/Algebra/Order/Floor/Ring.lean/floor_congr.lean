import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [Ring S] [LinearOrder S] [FloorRing R] [FloorRing S]

variable [FunLike F R S] [RingHomClass F R S] {a : R} {b : S}

theorem floor_congr (h : ∀ n : ℤ, (n : R) ≤ a ↔ (n : S) ≤ b) : ⌊a⌋ = ⌊b⌋ := (le_floor.2 <| (h _).1 <| floor_le _).antisymm <| le_floor.2 <| (h _).2 <| floor_le _

