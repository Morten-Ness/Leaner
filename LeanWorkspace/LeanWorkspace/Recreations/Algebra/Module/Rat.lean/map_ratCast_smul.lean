import Mathlib

variable {M M₂ : Type*}

theorem map_ratCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [DivisionRing S] [Module R M]
    [Module S M₂] (c : ℚ) (x : M) :
    f ((c : R) • x) = (c : S) • f x := by
  rw [Rat.cast_def, Rat.cast_def, div_eq_mul_inv, div_eq_mul_inv, mul_smul, mul_smul,
    map_intCast_smul f R S, map_inv_natCast_smul f R S]

