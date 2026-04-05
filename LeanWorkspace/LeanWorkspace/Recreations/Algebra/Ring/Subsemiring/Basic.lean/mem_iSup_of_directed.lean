import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subsemiring R} (hS : Directed (· ≤ ·) S)
    {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup S i hi⟩
  let U : Subsemiring R :=
    Subsemiring.mk' (⋃ i, (S i : Set R))
      (⨆ i, (S i).toSubmonoid) (Submonoid.coe_iSup_of_directed hS)
      (⨆ i, (S i).toAddSubmonoid) (AddSubmonoid.coe_iSup_of_directed hS)
  suffices ⨆ i, S i ≤ U by simpa [U] using @this x
  exact iSup_le fun i x hx ↦ Set.mem_iUnion.2 ⟨i, hx⟩

