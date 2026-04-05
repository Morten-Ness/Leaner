import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

theorem Finsupp.sum_mul (b : S) (s : α →₀ R) {f : α → R → S} :
    s.sum f * b = s.sum fun a c => f a c * b := by simp only [Finsupp.sum, Finset.sum_mul]

