import Mathlib

variable {R : Type*} [Semiring R] (r : R) (p : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ]
  [MulActionWithZero R S] (x : S)

theorem eval₂_smulOneHom_eq_smeval (R : Type*) [Semiring R] {S : Type*} [Semiring S] [Module R S]
    [IsScalarTower R S S] (p : R[X]) (x : S) :
    p.eval₂ RingHom.smulOneHom x = p.smeval x := by
  rw [Polynomial.smeval_eq_sum, eval₂_eq_sum]
  congr 1 with e a
  simp only [RingHom.smulOneHom_apply, smul_one_mul, Polynomial.smul_pow]

