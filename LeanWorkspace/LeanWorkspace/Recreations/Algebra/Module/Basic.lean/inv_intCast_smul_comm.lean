import Mathlib

variable {α R M M₂ : Type*}

theorem inv_intCast_smul_comm {α E : Type*} (R : Type*) [AddCommGroup E] [DivisionRing R]
    [Module R E] [DistribSMul α E] (n : ℤ) (s : α) (x : E) :
    (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x := (map_inv_intCast_smul (DistribSMul.toAddMonoidHom E s) R R n x).symm

