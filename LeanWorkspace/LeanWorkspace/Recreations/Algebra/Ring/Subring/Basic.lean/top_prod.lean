import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem top_prod (s : Subring S) : (⊤ : Subring R).prod s = s.comap (RingHom.snd R S) := ext fun x => by simp [Subring.mem_prod]

