import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [Ring S] [LinearOrder S] [FloorRing R] [FloorRing S]

variable [FunLike F R S] [RingHomClass F R S] {a : R} {b : S}

theorem map_fract (f : F) (hf : StrictMono f) (a : R) : fract (f a) = f (fract a) := by
  simp_rw [fract, map_sub, map_intCast, Int.map_floor _ hf]

