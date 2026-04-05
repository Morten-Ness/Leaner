import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem top_prod (s : Subsemigroup N) : (⊤ : Subsemigroup M).prod s = s.comap (MulHom.snd M N) := ext fun x => by simp [Subsemigroup.mem_prod, MulHom.coe_snd]

