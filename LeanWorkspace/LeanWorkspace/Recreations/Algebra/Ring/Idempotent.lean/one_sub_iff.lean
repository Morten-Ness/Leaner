import Mathlib

variable {R : Type*}

variable [NonAssocRing R] {a : R}

theorem one_sub_iff : IsIdempotentElem (1 - a) ↔ IsIdempotentElem a := ⟨fun h => sub_sub_cancel 1 a ▸ IsIdempotentElem.one_sub h, IsIdempotentElem.one_sub⟩

