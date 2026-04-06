FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : Finset ι}
    (h : s₁ ⊆ s₂) :
    s₁.affineCombination k p w = s₂.affineCombination k p (Set.indicator (↑s₁) w) := by
  classical
  by_cases hs₁ : s₁.Nonempty
  · rcases hs₁ with ⟨i0, hi0⟩
    simp only [Finset.affineCombination, hs₁, dif_pos hs₁]
    have hs₂ : s₂.Nonempty := ⟨i0, h hi0⟩
    simp only [dif_pos hs₂]
    have hsum_v :
        ∑ i ∈ s₂, Set.indicator (↑s₁) w i • (p i -ᵥ p i0) =
          ∑ i ∈ s₁, w i • (p i -ᵥ p i0) := by
      rw [← Finset.sum_attach s₂, ← Finset.sum_attach s₁]
      refine Finset.sum_bij (fun x _ => ⟨x.1, ?_⟩) ?_ ?_ ?_ ?_
      · exact x.2
      · intro x hx
        simp at hx
        simp [Set.indicator_of_mem, hx.1]
      · intro x hx
        simp at hx
        simp [hx.1]
      · intro x₁ x₂ hx₁ hx₂ hxeq
        exact Subtype.ext hxeq
      · intro y hy
        refine ⟨⟨y.1, h y.2⟩, ?_, ?_, ?_⟩
        · exact y.2
        · simp [Set.indicator_of_mem, y.2]
        · rfl
    have hsum_w :
        ∑ i ∈ s₂, Set.indicator (↑s₁) w i = ∑ i ∈ s₁, w i := by
      rw [← Finset.sum_attach s₂, ← Finset.sum_attach s₁]
      refine Finset.sum_bij (fun x _ => ⟨x.1, ?_⟩) ?_ ?_ ?_ ?_
      · exact x.2
      · intro x hx
        simp at hx
        simp [Set.indicator_of_mem, hx.1]
      · intro x hx
        simp at hx
        simp [hx.1]
      · intro x₁ x₂ hx₁ hx₂ hxeq
        exact Subtype.ext hxeq
      · intro y hy
        refine ⟨⟨y.1, h y.2⟩, ?_, ?_, ?_⟩
        · exact y.2
        · simp [Set.indicator_of_mem, y.2]
        · rfl
    rw [hsum_v, hsum_w]
  · have hs₁' : s₁ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs₁
    subst hs₁'
    simp [Finset.affineCombination]
