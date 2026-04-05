import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  {q : Submodule R M} {m : M}

theorem aeval_apply_smul_mem_of_le_comap'
    [Semiring A] [Algebra R A] [Module A M] [IsScalarTower R A M] (hm : m ∈ q) (p : R[X]) (a : A)
    (hq : q ≤ q.comap (Algebra.lsmul R R M a)) :
    Polynomial.aeval a p • m ∈ q := by
  induction p using Polynomial.induction_on with
  | Polynomial.C a => simpa using SMulMemClass.smul_mem a hm
  | add f₁ f₂ h₁ h₂ =>
    simp_rw [map_add, add_smul]
    exact Submodule.add_mem q h₁ h₂
  | monomial n t hmq =>
    dsimp only at hmq ⊢
    rw [pow_succ', mul_left_comm, map_mul, Polynomial.aeval_X, mul_smul]
    solve_by_elim

