import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

variable [Monoid N] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]

theorem smul_pow (r : M) (x : N) : ∀ n, (r • x) ^ n = r ^ n • x ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ', smul_pow _ _ n, smul_mul_smul_comm, ← pow_succ', ← pow_succ']
