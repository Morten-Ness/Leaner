import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem eq_zero_of_natDegree_lt_card_of_eval_eq_zero {R} [CommRing R] [IsDomain R]
    (p : R[X]) {ι} [Fintype ι] {f : ι → R} (hf : Function.Injective f)
    (heval : ∀ i, p.eval (f i) = 0) (hcard : natDegree p < Fintype.card ι) : p = 0 := by
  classical
  by_contra hp
  refine lt_irrefl #p.roots.toFinset ?_
  calc
    #p.roots.toFinset ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ natDegree p := Polynomial.card_roots' p
    _ < Fintype.card ι := hcard
    _ = Fintype.card (Set.range f) := (Set.card_range_of_injective hf).symm
    _ = #(Finset.univ.image f) := by rw [← Set.toFinset_card, Set.toFinset_range]
    _ ≤ #p.roots.toFinset := Finset.card_mono ?_
  intro _
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq,
    IsRoot.def, forall_exists_index, hp, not_false_eq_true]
  rintro x rfl
  exact heval _

