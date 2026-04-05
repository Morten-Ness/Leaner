import Mathlib

theorem Units.mem_posSubgroup {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    (u : Rˣ) : u ∈ Units.posSubgroup R ↔ (0 : R) < u := Iff.rfl

