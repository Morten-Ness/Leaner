import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_finset_sum_index [AddCommMonoid M] [CommMonoid N] {s : Finset ι} {g : ι → α →₀ M}
    {h : α → M → N} (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (∏ i ∈ s, (g i).prod h) = (∑ i ∈ s, g i).prod h := Finset.cons_induction_on s rfl fun a s has ih => by
    rw [prod_cons, ih, sum_cons, Finsupp.prod_add_index' h_zero h_add]

