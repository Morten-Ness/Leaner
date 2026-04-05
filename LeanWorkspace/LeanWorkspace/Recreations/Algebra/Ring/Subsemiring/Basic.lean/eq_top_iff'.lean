import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem eq_top_iff' (A : Subsemiring R) : A = ⊤ ↔ ∀ x : R, x ∈ A := eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

