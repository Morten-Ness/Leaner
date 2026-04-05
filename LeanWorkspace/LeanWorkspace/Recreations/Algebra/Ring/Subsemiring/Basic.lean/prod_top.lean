import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem prod_top (s : Subsemiring R) : s.prod (⊤ : Subsemiring S) = s.comap (RingHom.fst R S) := ext fun x => by simp [Subsemiring.mem_prod]

