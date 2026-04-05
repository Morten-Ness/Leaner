import Mathlib

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {h e f : L}

variable {m : M} {μ : R}

theorem lie_h_pow_toEnd_e (t : IsSl2Triple h e f)
    (hm : ⁅h, m⁆ = μ • m) (n : ℕ) :
    ⁅h, φ n⁆ = (μ + 2 * n) • φ n := by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply, Nat.cast_add, Nat.cast_one,
      leibniz_lie h, IsSl2Triple.lie_h_e_smul R t, smul_lie, ih, lie_smul, ← add_smul]
    congr 1
    ring

