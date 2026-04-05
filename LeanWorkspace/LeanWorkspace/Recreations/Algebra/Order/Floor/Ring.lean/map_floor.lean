import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [Ring S] [LinearOrder S] [FloorRing R] [FloorRing S]

variable [FunLike F R S] [RingHomClass F R S] {a : R} {b : S}

theorem map_floor (f : F) (hf : StrictMono f) (a : R) : ⌊f a⌋ = ⌊a⌋ := Int.floor_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

