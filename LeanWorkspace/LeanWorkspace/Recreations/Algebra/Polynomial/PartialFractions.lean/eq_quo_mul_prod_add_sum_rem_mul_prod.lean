import Mathlib

variable {R : Type*} [CommRing R]

theorem eq_quo_mul_prod_add_sum_rem_mul_prod [Nontrivial R] {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : R[X]) (r : ι → R[X]),
      (∀ i ∈ s, (r i).degree < (g i).degree) ∧
      f = q * (∏ i ∈ s, g i) + ∑ i ∈ s, r i * ∏ k ∈ s.erase i, g k := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.forall_mem_cons] at hg
    rw [Finset.coe_cons, Set.pairwise_insert] at hgg
    obtain ⟨q, r, -, hf⟩ := ih hg.2 hgg.1
    have hjs {j : ι} (hj : j ∈ s) : i ≠ j := fun hij => hi (hij ▸ hj)
    have hc (j : ι) : ∃ a b, j ∈ s → a * g i + b * g j = 1 :=
      if h : j ∈ s ∧ i ≠ j then
        (hgg.2 j h.1 h.2).1.elim fun a h => h.elim fun b h => ⟨a, b, fun _ => h⟩
      else
        ⟨0, 0, fun hj => (h ⟨hj, hjs hj⟩).elim⟩
    choose a b hab using hc
    refine ⟨(q + ∑ j ∈ s, r j * b j %ₘ g i) /ₘ g i + ∑ j ∈ s, (r j * b j /ₘ g i + r j * a j /ₘ g j),
      Function.update (fun j => r j * a j %ₘ g j) i ((q + ∑ j ∈ s, r j * b j %ₘ g i) %ₘ g i),
      ?_, hf.trans ?_⟩
    · rw [Finset.forall_mem_cons, Function.update_self]
      refine ⟨degree_modByMonic_lt _ hg.1, fun j hj => ?_⟩
      rw [Function.update_of_ne (hjs hj).symm]
      exact degree_modByMonic_lt _ (hg.2 j hj)
    · rw [Finset.prod_cons, Finset.sum_cons, Function.update_self, Finset.erase_cons, add_mul,
        add_add_add_comm, ← mul_assoc, ← add_mul, add_comm (_ * g i), ← mul_comm (g i),
        modByMonic_add_div, add_mul, add_assoc, add_right_inj, Finset.sum_mul,
        Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (hjs hj).symm, Finset.erase_cons_of_ne _ (hjs hj),
        Finset.prod_cons, ← Finset.mul_prod_erase s g hj]
      simp_rw [← mul_assoc, ← add_mul]
      refine congrArg (· * _) ?_
      rw [add_mul, add_mul, ← add_assoc, ← add_assoc, ← add_mul, ← mul_comm (g i),
        modByMonic_add_div, add_assoc, mul_right_comm (_ /ₘ g j),
        ← add_mul, add_comm (_ * g j) (_ %ₘ g j), mul_comm (_ /ₘ g j),
        modByMonic_add_div, mul_assoc, mul_assoc, ← mul_add,
        add_comm, hab j hj, mul_one]

