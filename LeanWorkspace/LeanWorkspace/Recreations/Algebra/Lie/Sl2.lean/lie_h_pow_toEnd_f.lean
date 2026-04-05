import Mathlib

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {h e f : L}

variable {m : M} {μ : R} {t : IsSl2Triple h e f}

variable (P : HasPrimitiveVectorWith t m μ)

theorem lie_h_pow_toEnd_f (n : ℕ) :
    ⁅h, ψ n⁆ = (μ - 2 * n) • ψ n := by
  induction n with
  | zero => simpa using P.lie_h
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply, Nat.cast_add, Nat.cast_one,
      leibniz_lie h, IsSl2Triple.lie_lie_smul_f t R, ← neg_smul, ih, lie_smul, smul_lie, ← add_smul]
    congr
    ring

