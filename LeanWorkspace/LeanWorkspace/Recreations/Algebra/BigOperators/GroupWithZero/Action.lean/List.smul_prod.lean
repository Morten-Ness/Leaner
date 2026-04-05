import Mathlib

variable {M N γ : Type*}

theorem smul_prod [Monoid M] [MulOneClass N] [MulAction M N] [IsScalarTower M N N]
    [SMulCommClass M N N] (l : List N) (m : M) :
    m ^ l.length • l.prod = (l.map (m • ·)).prod := by
  induction l with
  | nil => simp
  | cons head tail ih => simp [← ih, smul_mul_smul_comm, pow_succ']

