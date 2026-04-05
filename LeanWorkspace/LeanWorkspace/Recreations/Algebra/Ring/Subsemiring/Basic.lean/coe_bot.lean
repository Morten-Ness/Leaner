import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem coe_bot : ((⊥ : Subsemiring R) : Set R) = Set.range ((↑) : ℕ → R) := (Nat.castRingHom R).coe_rangeS

