import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem sum_filter_count_eq_countP [DecidableEq ι] (p : ι → Prop) [DecidablePred p] (l : List ι) :
    ∑ x ∈ l.toFinset with p x, l.count x = l.countP p := by
  simp [Finset.sum, sum_map_count_dedup_filter_eq_countP p l]

