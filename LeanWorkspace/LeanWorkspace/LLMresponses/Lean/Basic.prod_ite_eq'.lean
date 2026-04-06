FAIL
import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_ite_eq' [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.prod fun x v => ite (x = a) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 := by
  classical
  rw [Finsupp.prod]
  by_cases ha : a ∈ f.support
  · rw [if_pos ha]
    exact Finset.prod_eq_single a (by intro h; simp [h]) (by intro h hmem; simp [h] at ha)
  · rw [if_neg ha]
    refine Finset.prod_eq_one ?_
    intro x hx
    have hxa : x ≠ a := by
      intro h
      apply ha
      simpa [h] using hx
    simp [hxa]
