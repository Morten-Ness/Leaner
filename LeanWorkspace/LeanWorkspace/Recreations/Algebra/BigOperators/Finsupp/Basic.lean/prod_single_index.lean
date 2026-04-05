import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_single_index {a : α} {b : M} {h : α → M → N} (h_zero : h a 0 = 1) :
    (single a b).prod h = h a b := calc
    (single a b).prod h = ∏ x ∈ {a}, h x (single a b x) :=
      Finsupp.prod_of_support_subset _ support_single_subset h fun _ hx =>
        (mem_singleton.1 hx).symm ▸ h_zero
    _ = h a b := by simp

