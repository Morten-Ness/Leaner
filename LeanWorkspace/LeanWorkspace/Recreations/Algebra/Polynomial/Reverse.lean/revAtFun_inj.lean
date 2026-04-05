import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem revAtFun_inj {N : ℕ} : Function.Injective (Polynomial.revAtFun N) := by
  intro a b hab
  rw [← @Polynomial.revAtFun_invol N a, hab, Polynomial.revAtFun_invol]

