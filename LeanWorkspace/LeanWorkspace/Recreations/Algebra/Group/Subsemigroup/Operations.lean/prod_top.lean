import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem prod_top (s : Subsemigroup M) : s.prod (⊤ : Subsemigroup N) = s.comap (MulHom.fst M N) := ext fun x => by simp [Subsemigroup.mem_prod, MulHom.coe_fst]

