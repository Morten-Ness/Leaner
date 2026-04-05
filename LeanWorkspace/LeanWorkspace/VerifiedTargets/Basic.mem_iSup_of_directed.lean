import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S)
    {x : K} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  let s : Subfield K :=
    { __ := Subring.copy _ _ (Subring.coe_iSup_of_directed hS).symm
      inv_mem' := fun _ hx ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (S i).inv_mem hi⟩ }
  have : iSup S = s := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set K)) i) (Set.iUnion_subset fun _ ↦ le_iSup S _)
  exact this ▸ Set.mem_iUnion

