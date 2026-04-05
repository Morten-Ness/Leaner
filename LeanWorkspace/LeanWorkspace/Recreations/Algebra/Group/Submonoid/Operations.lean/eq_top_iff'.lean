import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S := eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

