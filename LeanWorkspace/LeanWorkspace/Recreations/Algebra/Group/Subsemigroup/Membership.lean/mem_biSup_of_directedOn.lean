import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_biSup_of_directedOn {ι} {p : ι → Prop} {K : ι → Subsemigroup M}
    (hK : DirectedOn ((· ≤ ·) on K) {i | p i})
    {x : M} : x ∈ (⨆ i, ⨆ (_h : p i), K i) ↔ ∃ i, p i ∧ x ∈ K i := by
  refine ⟨?_, fun ⟨i, hi', hi⟩ ↦ ?_⟩
  · suffices x ∈ closure (⋃ i, ⋃ (_ : p i), (K i : Set M)) → ∃ i, p i ∧ x ∈ K i by
      simpa only [closure_iUnion, closure_eq (K _)] using this
    refine fun hx ↦ closure_induction (fun _ ↦ ?_) ?_ hx
    · simp
    · rintro x y _ _ ⟨i, hip, hi⟩ ⟨j, hjp, hj⟩
      rcases hK i hip j hjp with ⟨k, hk, hki, hkj⟩
      exact ⟨k, hk, mul_mem (hki hi) (hkj hj)⟩
  · apply le_iSup (fun i ↦ ⨆ (_ : p i), K i) i
    simp [hi, hi']

-- TODO: this section can be generalized to `[MulMemClass B M] [CompleteLattice B]`
-- such that `complete_lattice.le` coincides with `set_like.le`

