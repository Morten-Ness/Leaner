import Mathlib

variable {R H : Type*}

theorem rank [Semiring R] [StrongRankCondition R] [AddCommMonoid H] [Module R H]
    [Module.Free R H] : Module.rank R Hᵐᵒᵖ = Module.rank R H := LinearEquiv.nonempty_equiv_iff_rank_eq.mp ⟨(opLinearEquiv R).symm⟩

