FAIL
import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem multiset_sum_sum [Zero M] [AddCommMonoid N] {f : α →₀ M} {h : α → M → Multiset N} :
    Multiset.sum (f.sum h) = f.sum fun a b => Multiset.sum (h a b) := by
  classical
  rw [Finsupp.sum]
  induction f.support.toMultiset using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      let b := f a
      have ha : a ∉ (f.erase a).support := by
        simp
      have hsplit : f = Finsupp.single a b + f.erase a := by
        ext x
        by_cases hx : x = a
        · subst hx
          simp [Finsupp.erase]
        · simp [Finsupp.erase, hx]
      rw [hsplit]
      simp [Finsupp.sum_add_index, ha, add_assoc, add_left_comm, add_comm]
