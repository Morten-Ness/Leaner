FAIL
import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mem_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S)
    {x : K} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  classical
  let U : Subfield K :=
    { carrier := ⋃ s ∈ S, (s : Set K)
      zero_mem' := by
        rcases Sne with ⟨s, hs⟩
        exact Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hs, s.zero_mem⟩⟩
      one_mem' := by
        rcases Sne with ⟨s, hs⟩
        exact Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hs, s.one_mem⟩⟩
      add_mem' := by
        intro a b ha hb
        rcases Set.mem_iUnion.1 ha with ⟨sa, ha⟩
        rcases Set.mem_iUnion.1 ha with ⟨hsaS, hasa⟩
        rcases Set.mem_iUnion.1 hb with ⟨sb, hb⟩
        rcases Set.mem_iUnion.1 hb with ⟨hsbS, hbsb⟩
        rcases hS sa hsaS sb hsbS with ⟨sc, hscS, hsa, hsb⟩
        exact Set.mem_iUnion.2 ⟨sc, Set.mem_iUnion.2 ⟨hscS, sc.add_mem (hsa hasa) (hsb hbsb)⟩⟩
      neg_mem' := by
        intro a ha
        rcases Set.mem_iUnion.1 ha with ⟨s, hs⟩
        rcases Set.mem_iUnion.1 hs with ⟨hsS, has⟩
        exact Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hsS, s.neg_mem has⟩⟩
      mul_mem' := by
        intro a b ha hb
        rcases Set.mem_iUnion.1 ha with ⟨sa, ha⟩
        rcases Set.mem_iUnion.1 ha with ⟨hsaS, hasa⟩
        rcases Set.mem_iUnion.1 hb with ⟨sb, hb⟩
        rcases Set.mem_iUnion.1 hb with ⟨hsbS, hbsb⟩
        rcases hS sa hsaS sb hsbS with ⟨sc, hscS, hsa, hsb⟩
        exact Set.mem_iUnion.2 ⟨sc, Set.mem_iUnion.2 ⟨hscS, sc.mul_mem (hsa hasa) (hsb hbsb)⟩⟩
      inv_mem' := by
        intro a ha
        rcases Set.mem_iUnion.1 ha with ⟨s, hs⟩
        rcases Set.mem_iUnion.1 hs with ⟨hsS, has⟩
        exact Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hsS, s.inv_mem has⟩⟩ }
  have hUle : ∀ s ∈ S, s ≤ U := by
    intro s hs x hx
    exact Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hs, hx⟩⟩
  have hleU : ∀ T : Subfield K, (∀ s ∈ S, s ≤ T) → U ≤ T := by
    intro T hT x hx
    rcases Set.mem_iUnion.1 hx with ⟨s, hs⟩
    rcases Set.mem_iUnion.1 hs with ⟨hsS, hxs⟩
    exact hT s hsS hxs
  have hsSup_eq : sSup S = U := by
    apply le_antisymm
    · exact sSup_le fun s hs => hUle s hs
    · refine sSup_le_iff.1 ?_
      exact hleU U hUle
  constructor
  · intro hx
    rw [hsSup_eq] at hx
    rcases Set.mem_iUnion.1 hx with ⟨s, hs⟩
    rcases Set.mem_iUnion.1 hs with ⟨hsS, hxs⟩
    exact ⟨s, hsS, hxs⟩
  · rintro ⟨s, hsS, hxs⟩
    rw [hsSup_eq]
    exact Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hsS, hxs⟩⟩
