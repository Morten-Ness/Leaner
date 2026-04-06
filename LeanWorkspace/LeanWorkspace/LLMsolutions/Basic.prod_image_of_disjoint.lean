FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_image_of_disjoint [DecidableEq ι] [PartialOrder ι] [OrderBot ι] {f : κ → ι} {g : ι → M}
    (hg_bot : g ⊥ = 1) {I : Finset κ} (hf_disj : (I : Set κ).PairwiseDisjoint f) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by
  classical
  have hinj : Set.InjOn f (I : Set κ) := by
    intro a ha b hb hab
    by_contra hne
    have hdisj := hf_disj ha hb hne
    rw [hab] at hdisj
    exact hdisj.ne_eq_bot hab
  simpa [Finset.prod_image, hinj, hg_bot] using
    (Finset.prod_image (s := I) (f := f) (g := g))
