import Mathlib

variable {α R M M₂ : Type*}

theorem inv_natCast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [DivisionSemiring S] [Module R E] [Module S E] (n : ℕ) (x : E) :
    (n⁻¹ : R) • x = (n⁻¹ : S) • x := map_inv_natCast_smul (AddMonoidHom.id E) R S n x

