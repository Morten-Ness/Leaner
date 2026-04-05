import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem Finsupp.sum_apply'' {A F : Type*} [AddZeroClass A] [AddCommMonoid F] [FunLike F γ B]
    (g : ι →₀ A) (k : ι → A → F) (x : γ)
    (h0 : (0 : F) x = 0) (hadd : ∀ (f g : F), (f + g : F) x = f x + g x) :
    g.sum k x = g.sum (fun i a ↦ k i a x) := by
  classical
  unfold Finsupp.sum
  induction g.support using Finset.induction with
  | empty => simp [h0]
  | insert i s hi ih => simp [Finset.sum_insert hi, hadd, ih]

