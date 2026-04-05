import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem mem_sInf {S : Set (Subsemiring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := Set.mem_iInter₂

