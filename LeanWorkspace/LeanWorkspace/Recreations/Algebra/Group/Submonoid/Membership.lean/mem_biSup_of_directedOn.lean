import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_biSup_of_directedOn {ι} {p : ι → Prop} {K : ι → Submonoid M} {i : ι} (hp : p i)
    (hK : DirectedOn ((· ≤ ·) on K) {i | p i})
    {x : M} : x ∈ (⨆ i, ⨆ (_h : p i), K i) ↔ ∃ i, p i ∧ x ∈ K i := by
  refine ⟨?_, fun ⟨i, hi', hi⟩ ↦ ?_⟩
  · suffices x ∈ closure (⋃ i, ⋃ (_ : p i), (K i : Set M)) → ∃ i, p i ∧ x ∈ K i by
      simpa only [closure_iUnion, closure_eq (K _)] using this
    refine fun hx ↦ closure_induction (fun _ ↦ ?_) ?_ ?_ hx
    · simp
    · exact ⟨i, hp, (K i).one_mem⟩
    · rintro x y _ _ ⟨i, hip, hi⟩ ⟨j, hjp, hj⟩
      rcases hK i hip j hjp with ⟨k, hk, hki, hkj⟩
      exact ⟨k, hk, mul_mem (hki hi) (hkj hj)⟩
  · apply le_iSup (fun i ↦ ⨆ (_ : p i), K i) i
    simp [hi, hi']

-- TODO: this section can be generalized to `[SubmonoidClass B M] [CompleteLattice B]`
-- such that `CompleteLattice.LE` coincides with `SetLike.LE`

