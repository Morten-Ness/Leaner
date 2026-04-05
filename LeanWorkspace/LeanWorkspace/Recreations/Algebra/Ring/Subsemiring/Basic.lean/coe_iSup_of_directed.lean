import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subsemiring R}
    (hS : Directed (· ≤ ·) S) : ((⨆ i, S i : Subsemiring R) : Set R) = ⋃ i, S i := Set.ext fun x ↦ by simp [Subsemiring.mem_iSup_of_directed hS]

