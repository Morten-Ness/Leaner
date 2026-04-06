FAIL
import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_hom₂_nonempty {l : List ι} (f : M → N → P)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (f₁ : ι → M) (f₂ : ι → N) (hl : l ≠ []) :
    (l.map fun i => f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod := by
  cases l with
  | nil =>
      cases hl rfl
  | cons x xs =>
      induction xs with
      | nil =>
          simp
      | cons y ys ih =>
          simp only [List.map_cons, List.prod_cons]
          rw [show
            (List.map (fun i => f (f₁ i) (f₂ i)) (y :: ys)).prod =
              f (List.map f₁ (y :: ys)).prod (List.map f₂ (y :: ys)).prod by
                exact prod_hom₂_nonempty f hf f₁ f₂ (by simp)]
          rw [← hf]
