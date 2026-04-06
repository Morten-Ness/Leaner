FAIL
import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_mul_eq_prod_mul_of_exists [Zero M] [CommMonoid N]
    {f : α →₀ M} {g : α → M → N} {n₁ n₂ : N}
    (a : α) (ha : a ∈ f.support)
    (h : g a (f a) * n₁ = g a (f a) * n₂) :
    f.prod g * n₁ = f.prod g * n₂ := by
  classical
  rw [Finsupp.prod]
  let s : Finset α := f.support.erase a
  have hs : f.support = insert a s := by
    simp [s, ha]
  rw [hs, Finset.prod_insert]
  · have h' := congrArg (fun y => (∏ b ∈ s, g b (f b)) * y) h
    simpa [mul_assoc] using h'
  · simp [s]
