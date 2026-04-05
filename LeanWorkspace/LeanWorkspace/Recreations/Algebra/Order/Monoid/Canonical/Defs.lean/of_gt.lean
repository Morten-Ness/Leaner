import Mathlib

variable {α : Type u}

theorem of_gt {M} [AddZeroClass M] [Preorder M] [CanonicallyOrderedAdd M]
    {x y : M} (h : x < y) : NeZero y := of_pos <| pos_of_gt h

-- 1 < p is still an often-used `Fact`, due to `Nat.Prime` implying it, and it implying `Nontrivial`
-- on `ZMod`'s ring structure. We cannot just set this to be any `x < y`, else that becomes a
-- metavariable and it will hugely slow down typeclass inference.

