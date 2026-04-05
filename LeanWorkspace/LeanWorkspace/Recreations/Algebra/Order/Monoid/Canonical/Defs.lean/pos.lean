import Mathlib

variable {α : Type u}

theorem pos {M} [AddZeroClass M] [PartialOrder M] [CanonicallyOrderedAdd M]
    (a : M) [NeZero a] : 0 < a := (zero_le a).lt_of_ne <| NeZero.out.symm

