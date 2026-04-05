import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem support_sum_eq_biUnion {α : Type*} {ι : Type*} {M : Type*} [DecidableEq α]
    [AddCommMonoid M] {g : ι → α →₀ M} (s : Finset ι)
    (h : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint (g i₁).support (g i₂).support) :
    (∑ i ∈ s, g i).support = s.biUnion fun i => (g i).support := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi
    simp only [hi, Finset.sum_insert, not_false_iff, biUnion_insert]
    intro hs
    rw [Finsupp.support_add_eq, hs]
    rw [hs, Finset.disjoint_biUnion_right]
    intro j hj
    exact h _ _ (ne_of_mem_of_not_mem hj hi).symm

