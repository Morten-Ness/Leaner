import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem single_finset_sum [AddCommMonoid M] (s : Finset ι) (f : ι → M) (a : α) :
    single a (∑ b ∈ s, f b) = ∑ b ∈ s, single a (f b) := by
  trans
  · apply Finsupp.single_multiset_sum
  · rw [Multiset.map_map]
    rfl

