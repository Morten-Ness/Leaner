import Mathlib

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {h e f : L}

variable {m : M} {μ : R} {t : IsSl2Triple h e f}

variable (P : HasPrimitiveVectorWith t m μ)

theorem lie_e_pow_succ_toEnd_f (n : ℕ) :
    ⁅e, ψ (n + 1)⁆ = ((n + 1) * (μ - n)) • ψ n := by
  induction n with
  | zero =>
      simp only [zero_add, pow_one, toEnd_apply_apply, Nat.cast_zero, sub_zero, one_mul,
        pow_zero, Module.End.one_apply, leibniz_lie e, t.lie_e_f, P.lie_e, P.lie_h, lie_zero,
        add_zero]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply, leibniz_lie e, t.lie_e_f,
      IsSl2Triple.HasPrimitiveVectorWith.lie_h_pow_toEnd_f P, ih, lie_smul, IsSl2Triple.HasPrimitiveVectorWith.lie_f_pow_toEnd_f P, ← add_smul,
      Nat.cast_add, Nat.cast_one]
    congr
    ring

