import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem smul_mem_smul {r} {n} (hr : r ∈ I) (hn : n ∈ N) : r • n ∈ I • N := AddSubmonoid.smul_mem_smul hr hn

