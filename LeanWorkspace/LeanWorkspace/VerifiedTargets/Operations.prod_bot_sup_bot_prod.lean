import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem prod_bot_sup_bot_prod (s : Submonoid M) (t : Submonoid N) :
    (Submonoid.prod s ⊥) ⊔ (Submonoid.prod ⊥ t) = Submonoid.prod s t := (le_antisymm (sup_le (Submonoid.prod_mono (le_refl s) bot_le) (Submonoid.prod_mono bot_le (le_refl t))))
    fun p hp => Prod.fst_mul_snd p ▸ mul_mem
        ((le_sup_left : Submonoid.prod s ⊥ ≤ Submonoid.prod s ⊥ ⊔ Submonoid.prod ⊥ t) ⟨hp.1, Set.mem_singleton 1⟩)
        ((le_sup_right : Submonoid.prod ⊥ t ≤ Submonoid.prod s ⊥ ⊔ Submonoid.prod ⊥ t) ⟨Set.mem_singleton 1, hp.2⟩)

