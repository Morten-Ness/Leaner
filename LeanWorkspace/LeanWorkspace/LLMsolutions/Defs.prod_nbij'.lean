FAIL
import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

theorem prod_nbij' (i : ι → κ) (j : κ → ι) (hi : ∀ a ∈ s, i a ∈ t) (hj : ∀ a ∈ t, j a ∈ s)
    (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a)
    (h : ∀ a ∈ s, f a = g (i a)) : ∏ x ∈ s, f x = ∏ x ∈ t, g x := by
  classical
  exact Finset.prod_nbij i hi j hj left_inv right_inv h
