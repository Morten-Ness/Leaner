import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem univ_sum_single_apply' [AddCommMonoid M] [Fintype α] (i : α) (m : M) :
    ∑ j : α, single j m i = m := by
  simp_rw [single, coe_mk]
  classical rw [Finset.sum_pi_single]
  simp

