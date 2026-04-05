import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_indicator_index_eq_prod_attach [Zero M] [CommMonoid N]
    {s : Finset α} (f : ∀ a ∈ s, M) {h : α → M → N} (h_zero : ∀ a ∈ s, h a 0 = 1) :
    (indicator s f).prod h = ∏ x ∈ s.attach, h ↑x (f x x.2) := by
  rw [Finsupp.prod_of_support_subset _ (support_indicator_subset _ _) h h_zero, ← prod_attach]
  refine Finset.prod_congr rfl (fun _ _ => ?_)
  rw [indicator_of_mem]

