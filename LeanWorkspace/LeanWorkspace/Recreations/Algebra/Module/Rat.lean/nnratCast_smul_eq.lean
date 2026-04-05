import Mathlib

variable {M M₂ : Type*}

theorem nnratCast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [DivisionSemiring S] [Module R E] [Module S E] (r : ℚ≥0) (x : E) : (r : R) • x = (r : S) • x := map_nnratCast_smul (AddMonoidHom.id E) R S r x

