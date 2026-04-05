import Mathlib

variable {M M₂ : Type*}

theorem ratCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
    [DivisionRing S] [Module R E] [Module S E] (r : ℚ) (x : E) : (r : R) • x = (r : S) • x := map_ratCast_smul (AddMonoidHom.id E) R S r x

