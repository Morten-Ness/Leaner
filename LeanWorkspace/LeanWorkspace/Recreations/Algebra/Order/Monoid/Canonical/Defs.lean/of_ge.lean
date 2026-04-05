import Mathlib

variable {α : Type u}

theorem of_ge {M} [AddZeroClass M] [PartialOrder M] [CanonicallyOrderedAdd M]
    {x y : M} [NeZero x] (h : x ≤ y) : NeZero y := of_pos <| lt_of_lt_of_le (NeZero.pos x) h

