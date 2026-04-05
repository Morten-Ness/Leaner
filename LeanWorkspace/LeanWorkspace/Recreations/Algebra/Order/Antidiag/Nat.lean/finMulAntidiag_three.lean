import Mathlib

open scoped ArithmeticFunction ArithmeticFunction.omega in -- access notation `ω`

private def primeFactorsPiBij (d n : ℕ) :
    ∀ f ∈ (n.primeFactors.pi fun _ => (Finset.univ : Finset <| Fin d)), Fin d → ℕ := fun f _ i => ∏ p ∈ {p ∈ n.primeFactors.attach | f p.1 p.2 = i}, p


private theorem primeFactorsPiBij_img (d n : ℕ) (hn : Squarefree n)
    (f : (p : ℕ) → p ∈ n.primeFactors → Fin d) (hf : f ∈ pi n.primeFactors fun _ => Finset.univ) :
    Nat.primeFactorsPiBij d n f hf ∈ Nat.finMulAntidiag d n := by
  rw [Nat.mem_finMulAntidiag]
  refine ⟨?_, hn.ne_zero⟩
  unfold Nat.primeFactorsPiBij
  rw [prod_fiberwise_of_maps_to, prod_attach (f := fun x => x)]
  · apply prod_primeFactors_of_squarefree hn
  · apply fun _ _ => Finset.mem_univ _


private theorem primeFactorsPiBij_inj (d n : ℕ)
    (f : (p : ℕ) → p ∈ n.primeFactors → Fin d) (hf : f ∈ pi n.primeFactors fun _ => Finset.univ)
    (g : (p : ℕ) → p ∈ n.primeFactors → Fin d) (hg : g ∈ pi n.primeFactors fun _ => Finset.univ) :
    Nat.primeFactorsPiBij d n f hf = Nat.primeFactorsPiBij d n g hg → f = g := by
  contrapose!
  simp_rw [Function.ne_iff]
  intro ⟨p, hp, hfg⟩
  use f p hp
  dsimp only [Nat.primeFactorsPiBij]
  apply ne_of_mem_of_not_mem (s := {x | p ∣ x}) <;> simp_rw [Set.mem_setOf_eq]
  · rw [Finset.prod_filter]
    convert Finset.dvd_prod_of_mem _ (mem_attach (n.primeFactors) ⟨p, hp⟩)
    rw [if_pos rfl]
  · rw [mem_primeFactors] at hp
    rw [Prime.dvd_finset_prod_iff hp.1.prime]
    push Not
    intro q hq
    rw [Nat.prime_dvd_prime_iff_eq hp.1 (Nat.prime_of_mem_primeFactorsList
      <| List.mem_toFinset.mp q.2)]
    rintro rfl
    rw [(mem_filter.mp hq).2] at hfg
    exact hfg rfl


private theorem primeFactorsPiBij_surj (d n : ℕ) (hn : Squarefree n)
    (t : Fin d → ℕ) (ht : t ∈ Nat.finMulAntidiag d n) : ∃ (g : _)
    (hg : g ∈ pi n.primeFactors fun _ => Finset.univ), Nat.primeFactorsPiBij d n g hg = t := by
  have existsUnique := fun (p : ℕ) (hp : p ∈ n.primeFactors) =>
    (Nat.finMulAntidiag_existsUnique_prime_dvd hn
      (mem_primeFactors_iff_mem_primeFactorsList.mp hp) t ht)
  choose f hf hf_unique using existsUnique
  refine ⟨f, ?_, ?_⟩
  · simp only [mem_pi, Finset.mem_univ, forall_true_iff]
  funext i
  have : t i ∣ n := Nat.dvd_of_mem_finMulAntidiag ht _
  trans (∏ p ∈ n.primeFactors.attach, if p.1 ∣ t i then p else 1)
  · rw [Nat.primeFactorsPiBij, ← prod_filter]
    congr
    grind
  rw [prod_attach (f := fun p => if p ∣ t i then p else 1), ← Finset.prod_filter]
  rw [primeFactors_filter_dvd_of_dvd hn.ne_zero this]
  exact prod_primeFactors_of_squarefree <| hn.squarefree_of_dvd this


private theorem card_finMulAntidiag_pi (d n : ℕ) (hn : Squarefree n) :
    #(n.primeFactors.pi fun _ => (Finset.univ : Finset <| Fin d)) =
      #(Nat.finMulAntidiag d n) := by
  apply Finset.card_bij (Nat.primeFactorsPiBij d n) (primeFactorsPiBij_img d n hn)
    (primeFactorsPiBij_inj d n) (primeFactorsPiBij_surj d n hn)


theorem finMulAntidiag_three {n : ℕ} (a) (ha : a ∈ Nat.finMulAntidiag 3 n) : a 0 * a 1 * a 2 = n := by
  rw [← (Nat.mem_finMulAntidiag.mp ha).1, Fin.prod_univ_three a]

