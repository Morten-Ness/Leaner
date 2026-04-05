import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem prod_bot_sup_bot_prod (s : Subring R) (t : Subring S) : s.prod ⊥ ⊔ Subring.prod ⊥ t = s.prod t := le_antisymm (sup_le (Subring.prod_mono_right s bot_le) (Subring.prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ Subring.prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : Subring.prod ⊥ t ≤ s.prod ⊥ ⊔ Subring.prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

