import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

theorem le_prod_nonempty_of_submultiplicative [IsOrderedMonoid N] (f : M → N)
    (h_mul : ∀ x y, f (x * y) ≤ f x * f y) {s : Finset ι} (hs : s.Nonempty) (g : ι → M) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := Finset.le_prod_nonempty_of_submultiplicative_on_pred f (fun _ ↦ True) (fun x y _ _ ↦ h_mul x y)
    (fun _ _ _ _ ↦ trivial) g s hs fun _ _ ↦ trivial

