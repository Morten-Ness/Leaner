FAIL
import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem disjoint_finset_sum_right {i : Finset ι} {f : ι → Multiset α}
    {a : Multiset α} : Disjoint a (i.sum f) ↔ ∀ b ∈ i, Disjoint a (f b) := by
  classical
  induction i using Finset.induction_on with
  | empty =>
      constructor
      · intro h
        intro b hb
        simpa using hb
      · intro h
        exact disjoint_zero_right
  | @insert b s hb ih =>
      simp [hb, ih, disjoint_add_right]
