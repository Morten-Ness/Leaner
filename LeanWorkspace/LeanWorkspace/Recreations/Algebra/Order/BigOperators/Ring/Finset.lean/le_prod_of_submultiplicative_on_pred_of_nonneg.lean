import Mathlib

variable {ι R S : Type*}

variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : ι → R} {s t : Finset ι}

theorem le_prod_of_submultiplicative_on_pred_of_nonneg {M : Type*} [CommMonoid M] (f : M → R)
    (p : M → Prop) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 ≤ 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Finset ι) (g : ι → M) (hps : ∀ a, a ∈ s → p (g a)) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  apply le_trans (Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg f p h_nonneg h_one
    h_mul hp_mul _ ?_) (by simp [Multiset.map_map])
  intro _ ha
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp ha
  exact hps i hi

