import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem prod_top (s : Subring R) : s.prod (⊤ : Subring S) = s.comap (RingHom.fst R S) := ext fun x => by simp [Subring.mem_prod]

