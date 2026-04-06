FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_partition (R : Setoid ι) [DecidableRel R.r] :
    ∏ x ∈ s, f x = ∏ xbar ∈ s.image (Quotient.mk _), ∏ y ∈ s with ⟦y⟧ = xbar, f y := by
  classical
  let t : Finset (Quotient R) := s.image (Quotient.mk R)
  let F : Quotient R → Finset ι := fun xbar => s.filter (fun y => ⟦y⟧ = xbar)
  have hdisj : Set.PairwiseDisjoint t.toSet F := by
    intro x hx y hy hxy
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    have hxz : ⟦z⟧ = x := by
      simpa [F] using (Finset.mem_filter.mp hz1).2
    have hyz : ⟦z⟧ = y := by
      simpa [F] using (Finset.mem_filter.mp hz2).2
    apply hxy
    exact hxz.trans hyz.symm
  have hunion : s.biUnion (fun xbar => s.filter (fun y => ⟦y⟧ = xbar)) = s := by
    apply Finset.ext
    intro y
    simp only [Finset.mem_biUnion, Finset.mem_filter, t, true_and]
    constructor
    · intro hy
      rcases hy with ⟨xbar, hxbar, hyin, _⟩
      exact hyin
    · intro hy
      refine ⟨⟦y⟧, ?_, hy, rfl⟩
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  calc
    ∏ x ∈ s, f x = ∏ x ∈ s.biUnion F, f x := by rw [hunion]
    _ = ∏ xbar ∈ t, ∏ y ∈ F xbar, f y := by
      rw [Finset.prod_biUnion]
      · intro x hx y hy hxy
        exact hdisj hx hy hxy
    _ = ∏ xbar ∈ s.image (Quotient.mk _), ∏ y ∈ s with ⟦y⟧ = xbar, f y := by
      rfl
