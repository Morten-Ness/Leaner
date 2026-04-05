import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_image_of_disjoint [DecidableEq ι] [PartialOrder ι] [OrderBot ι] {f : κ → ι} {g : ι → M}
    (hg_bot : g ⊥ = 1) {I : Finset κ} (hf_disj : (I : Set κ).PairwiseDisjoint f) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by
  refine Finset.prod_image_of_pairwise_eq_one <| hf_disj.imp fun i j hdisj hfij ↦ ?_
  rw [Function.onFun, ← hfij, disjoint_self] at hdisj
  rw [hdisj, hg_bot]

