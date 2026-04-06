import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_hom_add_index [AddZeroClass M] [CommMonoid N] {f g : α →₀ M}
    (h : α → Multiplicative M →* N) :
    ((f + g).prod fun a b => h a (Multiplicative.ofAdd b)) =
      (f.prod fun a b => h a (Multiplicative.ofAdd b)) *
        g.prod fun a b => h a (Multiplicative.ofAdd b) := by
  classical
  simpa using
    Finsupp.prod_add_index (f := f) (g := g) (h := fun a b => h a (Multiplicative.ofAdd b))
      (by simp)
      (by
        intro a b₁ b₂
        simpa using map_mul (h a) (Multiplicative.ofAdd b₁) (Multiplicative.ofAdd b₂))
