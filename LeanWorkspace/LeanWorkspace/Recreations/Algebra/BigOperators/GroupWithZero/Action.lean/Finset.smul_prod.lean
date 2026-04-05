import Mathlib

variable {M N γ : Type*}

variable {ι : Type*}

theorem smul_prod
    [CommMonoid N] [Monoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset ι) (b : M) (f : ι → N) :
    b ^ s.card • ∏ x ∈ s, f x = ∏ x ∈ s, b • f x := by
  have : Multiset.map (fun (x : ι) ↦ b • f x) s.val =
      Multiset.map (fun x ↦ b • x) (Multiset.map f s.val) := by
    simp only [Multiset.map_map, Function.comp_apply]
  simp_rw [prod_eq_multiset_prod, card_def, this, ← Multiset.smul_prod _ b, Multiset.card_map]

