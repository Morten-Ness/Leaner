import Mathlib

variable {α R M M₂ : Type*}

theorem inv_natCast_smul_comm {α E : Type*} (R : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [Module R E] [DistribSMul α E] (n : ℕ) (s : α) (x : E) :
    (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x := (map_inv_natCast_smul (DistribSMul.toAddMonoidHom E s) R R n x).symm

