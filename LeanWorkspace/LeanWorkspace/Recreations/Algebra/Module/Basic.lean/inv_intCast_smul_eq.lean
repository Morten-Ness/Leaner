import Mathlib

variable {α R M M₂ : Type*}

theorem inv_intCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
    [DivisionRing S] [Module R E] [Module S E] (n : ℤ) (x : E) : (n⁻¹ : R) • x = (n⁻¹ : S) • x := map_inv_intCast_smul (AddMonoidHom.id E) R S n x

