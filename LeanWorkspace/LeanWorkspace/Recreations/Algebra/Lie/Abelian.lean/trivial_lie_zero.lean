import Mathlib

theorem trivial_lie_zero (L : Type v) (M : Type w) [Bracket L M] [Zero M] [LieModule.IsTrivial L M]
    (x : L) (m : M) : ⁅x, m⁆ = 0 := LieModule.IsTrivial.trivial x m

