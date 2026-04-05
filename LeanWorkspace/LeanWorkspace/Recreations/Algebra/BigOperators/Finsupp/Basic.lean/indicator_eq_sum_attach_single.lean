import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem indicator_eq_sum_attach_single [AddCommMonoid M] {s : Finset α} (f : ∀ a ∈ s, M) :
    indicator s f = ∑ x ∈ s.attach, single ↑x (f x x.2) := by
  rw [← Finsupp.sum_single (indicator s f), sum, sum_subset (support_indicator_subset _ _), ← sum_attach]
  · refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [indicator_of_mem]
  · intro i _ hi
    rw [notMem_support_iff.mp hi, single_zero]

