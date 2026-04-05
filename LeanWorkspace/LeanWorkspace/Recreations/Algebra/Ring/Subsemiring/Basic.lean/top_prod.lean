import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem top_prod (s : Subsemiring S) : (⊤ : Subsemiring R).prod s = s.comap (RingHom.snd R S) := ext fun x => by simp [Subsemiring.mem_prod]

