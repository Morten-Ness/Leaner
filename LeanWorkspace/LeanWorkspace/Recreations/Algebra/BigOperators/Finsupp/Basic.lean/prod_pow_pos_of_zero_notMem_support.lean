import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_pow_pos_of_zero_notMem_support {f : ℕ →₀ ℕ} (nhf : 0 ∉ f.support) :
    0 < f.prod (· ^ ·) := Nat.pos_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun _ hf =>
    pow_ne_zero _ fun H => by subst H; exact nhf hf

