import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

variable {S : Submonoid M} [Fintype S]

theorem card_bot {_ : Fintype (⊥ : Submonoid M)} : card (⊥ : Submonoid M) = 1 := card_eq_one_iff.2
    ⟨⟨(1 : M), Set.mem_singleton 1⟩, fun ⟨_y, hy⟩ => Subtype.ext <| mem_bot.1 hy⟩

