import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem support_finset_sum [DecidableEq β] [AddCommMonoid M] {s : Finset α} {f : α → β →₀ M} :
    (Finset.sum s f).support ⊆ s.biUnion fun x => (f x).support := by
  rw [← Finset.sup_eq_biUnion]
  induction s using Finset.cons_induction_on with
  | empty => rfl
  | cons _ _ _ ih =>
    rw [Finset.sum_cons, Finset.sup_cons]
    exact support_add.trans (Finset.union_subset_union (Finset.Subset.refl _) ih)

