import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

variable {ι : Type*} {p : ι → Ideal R} {S : Finset ι}

theorem iSup_torsionBySet_ideal_eq_torsionBySet_iInf
    (hp : (S : Set ι).Pairwise fun i j => p i ⊔ p j = ⊤) :
    ⨆ i ∈ S, Submodule.torsionBySet R M (p i) = Submodule.torsionBySet R M ↑(⨅ i ∈ S, p i) := by
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  apply le_antisymm
  · apply iSup_le _
    intro i
    apply iSup_le _
    intro is
    apply Submodule.torsionBySet_le_torsionBySet_of_subset
    exact (iInf_le (fun i => ⨅ _ : i ∈ S, p i) i).trans (iInf_le _ is)
  · intro x hx
    rw [mem_iSup_finset_iff_exists_sum]
    obtain ⟨μ, hμ⟩ :=
      (mem_iSup_finset_iff_exists_sum _ _).mp
        ((Ideal.eq_top_iff_one _).mp <| (Ideal.iSup_iInf_eq_top_iff_pairwise h _).mpr hp)
    refine ⟨fun i => ⟨(μ i : R) • x, ?_⟩, ?_⟩
    · rw [Submodule.mem_torsionBySet_iff] at hx ⊢
      rintro ⟨a, ha⟩
      rw [smul_smul]
      suffices a * μ i ∈ ⨅ i ∈ S, p i from hx ⟨_, this⟩
      rw [mem_iInf]
      intro j
      rw [mem_iInf]
      intro hj
      by_cases ij : j = i
      · rw [ij]
        exact Ideal.mul_mem_right _ _ ha
      · have := coe_mem (μ i)
        simp only [mem_iInf] at this
        exact Ideal.mul_mem_left _ _ (this j hj ij)
    · rw [← Finset.sum_smul, hμ, one_smul]

