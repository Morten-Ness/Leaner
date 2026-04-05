import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

theorem mem_normalizer_fintype {S : Set G} [Finite S] {x : G} (h : ∀ n, n ∈ S → x * n * x⁻¹ ∈ S) :
    x ∈ Subgroup.normalizer S := by
  haveI := Classical.propDecidable; cases nonempty_fintype S
  exact fun n =>
    ⟨h n, fun h₁ =>
      have heq : (fun n => x * n * x⁻¹) '' S = S :=
        Set.eq_of_subset_of_card_le (fun n ⟨y, hy⟩ => hy.2 ▸ h y hy.1)
          (by rw [Set.card_image_of_injective S conj_injective])
      have : x * n * x⁻¹ ∈ (fun n => x * n * x⁻¹) '' S := heq.symm ▸ h₁
      let ⟨y, hy⟩ := this
      conj_injective hy.2 ▸ hy.1⟩

