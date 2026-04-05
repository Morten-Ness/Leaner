import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a : R}

variable {S : Type*} [Semiring S] [LinearOrder S] [FloorSemiring S] {b : S}

variable {F : Type*} [FunLike F R S] [RingHomClass F R S]

theorem map_ceil (f : F) (hf : StrictMono f) (a : R) : ⌈f a⌉₊ = ⌈a⌉₊ := Nat.ceil_congr fun n => by rw [← map_natCast f, hf.le_iff_le]

