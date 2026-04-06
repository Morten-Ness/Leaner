FAIL
import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_sSup_of_directedOn {S : Set (Submonoid M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : M} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  classical
  let P : Submonoid M :=
    {
      carrier := {x : M | ∃ s ∈ S, x ∈ s}
      one_mem' := by
        rcases Sne with ⟨s, hs⟩
        exact ⟨s, hs, s.one_mem⟩
      mul_mem' := by
        intro a b ha hb
        rcases ha with ⟨sa, hsa, ha⟩
        rcases hb with ⟨sb, hsb, hb⟩
        rcases hS hsa hsb with ⟨sc, hsc, hle_a, hle_b⟩
        exact ⟨sc, hsc, hle_a ha, hle_b hb⟩
    }
  have h_upper : ∀ s ∈ S, s ≤ P := by
    intro s hs x hx
    exact ⟨s, hs, hx⟩
  have h_least : ∀ Q : Submonoid M, (∀ s ∈ S, s ≤ Q) → P ≤ Q := by
    intro Q hQ x hx
    rcases hx with ⟨s, hs, hx⟩
    exact hQ s hs hx
  have hsSup_eq : sSup S = P := by
    apply le_antisymm
    · exact sSup_le h_upper
    · exact h_least (sSup S) (by intro s hs; exact le_sSup hs)
  constructor
  · intro hx
    rw [hsSup_eq] at hx
    exact hx
  · rintro ⟨s, hs, hx⟩
    rw [hsSup_eq]
    exact ⟨s, hs, hx⟩
