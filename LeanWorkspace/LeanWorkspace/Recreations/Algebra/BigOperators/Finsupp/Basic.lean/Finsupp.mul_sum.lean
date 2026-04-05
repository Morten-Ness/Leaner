import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

theorem Finsupp.mul_sum (b : S) (s : α →₀ R) {f : α → R → S} :
    b * s.sum f = s.sum fun a c => b * f a c := by simp only [Finsupp.sum, Finset.mul_sum]

