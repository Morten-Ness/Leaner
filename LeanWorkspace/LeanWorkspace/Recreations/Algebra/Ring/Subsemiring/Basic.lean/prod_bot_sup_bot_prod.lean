import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem prod_bot_sup_bot_prod (s : Subsemiring R) (t : Subsemiring S) :
    s.prod ⊥ ⊔ Subsemiring.prod ⊥ t = s.prod t := le_antisymm (sup_le (Subsemiring.prod_mono_right s bot_le) (Subsemiring.prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ Subsemiring.prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : Subsemiring.prod ⊥ t ≤ s.prod ⊥ ⊔ Subsemiring.prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

