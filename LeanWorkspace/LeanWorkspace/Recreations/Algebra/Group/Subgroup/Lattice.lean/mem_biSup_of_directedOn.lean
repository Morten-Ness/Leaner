import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_biSup_of_directedOn {ι} {p : ι → Prop} {K : ι → Subgroup G} {i : ι} (hp : p i)
    (hK : DirectedOn ((· ≤ ·) on K) {i | p i})
    {x : G} : x ∈ (⨆ i, ⨆ (_h : p i), K i) ↔ ∃ i, p i ∧ x ∈ K i := by
  -- Could use the `Submonoid` version, but we limit the imports here
  refine ⟨?_, fun ⟨i, hi', hi⟩ ↦ ?_⟩
  · suffices x ∈ Subgroup.closure (⋃ i, ⋃ (_ : p i), (K i : Set G)) → ∃ i, p i ∧ x ∈ K i by
      simpa only [Subgroup.closure_iUnion, Subgroup.closure_eq (K _)] using this
    refine fun hx ↦ Subgroup.closure_induction (fun _ ↦ ?_) ?_ ?_ ?_ hx
    · simp
    · exact ⟨i, hp, (K i).one_mem⟩
    · rintro x y _ _ ⟨i, hip, hi⟩ ⟨j, hjp, hj⟩
      rcases hK i hip j hjp with ⟨k, hk, hki, hkj⟩
      exact ⟨k, hk, mul_mem (hki hi) (hkj hj)⟩
    · rintro _ _ ⟨i, hi', hi⟩
      exact ⟨i, hi', inv_mem hi⟩
  · apply le_iSup (fun i ↦ ⨆ (_ : p i), K i) i
    simp [hi, hi']

