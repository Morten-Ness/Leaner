import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [Ring S] [LinearOrder S] [FloorRing R] [FloorRing S]

variable [FunLike F R S] [RingHomClass F R S] {a : R} {b : S}

theorem ceil_congr (h : ∀ n : ℤ, a ≤ n ↔ b ≤ n) : ⌈a⌉ = ⌈b⌉ := (ceil_le.2 <| (h _).2 <| le_ceil _).antisymm <| ceil_le.2 <| (h _).1 <| le_ceil _

