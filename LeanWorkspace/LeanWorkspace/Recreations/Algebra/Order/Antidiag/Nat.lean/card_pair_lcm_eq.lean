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


private def f {n : ℕ} : ∀ a ∈ Nat.finMulAntidiag 3 n, ℕ × ℕ := fun a _ => (a 0 * a 1, a 0 * a 2)


private theorem f_img {n : ℕ} (hn : Squarefree n) (a : Fin 3 → ℕ)
    (ha : a ∈ Nat.finMulAntidiag 3 n) :
    f a ha ∈ Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors) := by
  rw [mem_filter, Finset.mem_product, mem_divisors, mem_divisors]
  refine ⟨⟨⟨?_, hn.ne_zero⟩, ⟨?_, hn.ne_zero⟩⟩, ?_⟩ <;> rw [f, ← Nat.finMulAntidiag_three a ha]
  · apply dvd_mul_right
  · use a 1; ring
  dsimp only
  rw [lcm_mul_left, Nat.Coprime.lcm_eq_mul]
  · ring
  refine coprime_of_squarefree_mul (hn.squarefree_of_dvd ?_)
  use a 0; rw [← Nat.finMulAntidiag_three a ha]; ring


private theorem f_inj {n : ℕ} (a : Fin 3 → ℕ) (ha : a ∈ Nat.finMulAntidiag 3 n)
    (b : Fin 3 → ℕ) (hb : b ∈ Nat.finMulAntidiag 3 n) (hfab : f a ha = f b hb) :
    a = b := by
  obtain ⟨hfab1, hfab2⟩ := Prod.mk.inj hfab
  have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2 := by
    rw [Nat.finMulAntidiag_three a ha, hfab1, Nat.finMulAntidiag_three b hb]
  have hab2 : a 2 = b 2 := by
    rw [← mul_right_inj' <| mul_ne_zero (Nat.ne_zero_of_mem_finMulAntidiag ha 0)
      (Nat.ne_zero_of_mem_finMulAntidiag ha 1)]
    exact hprods
  have hab0 : a 0 = b 0 := by
    rw [hab2] at hfab2
    exact (mul_left_inj' <| Nat.ne_zero_of_mem_finMulAntidiag hb 2).mp hfab2;
  have hab1 : a 1 = b 1 := by
    rw [hab0] at hfab1
    exact (mul_right_inj' <| Nat.ne_zero_of_mem_finMulAntidiag hb 0).mp hfab1;
  funext i; fin_cases i <;> assumption


private theorem f_surj {n : ℕ} (hn : n ≠ 0) (b : ℕ × ℕ)
    (hb : b ∈ Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors)) :
    ∃ (a : Fin 3 → ℕ) (ha : a ∈ Nat.finMulAntidiag 3 n), f a ha = b := by
  dsimp only at hb
  let g := b.fst.gcd b.snd
  let a := ![g, b.fst / g, b.snd / g]
  have ha : a ∈ Nat.finMulAntidiag 3 n := by
    rw [Nat.mem_finMulAntidiag]
    rw [mem_filter, Finset.mem_product] at hb
    refine ⟨?_, hn⟩
    · rw [Fin.prod_univ_three a]
      dsimp only [a, Matrix.cons_val]
      rw [Nat.mul_div_cancel_left' (Nat.gcd_dvd_left _ _), ← hb.2, lcm,
        Nat.mul_div_assoc b.fst (Nat.gcd_dvd_right b.fst b.snd)]
  use a; use ha
  apply Prod.ext <;> dsimp only [a, Matrix.cons_val]
    <;> apply Nat.mul_div_cancel'
  · apply Nat.gcd_dvd_left
  · apply Nat.gcd_dvd_right


theorem card_pair_lcm_eq {n : ℕ} (hn : Squarefree n) :
    #{p ∈ (n.divisors ×ˢ n.divisors) | p.1.lcm p.2 = n} = 3 ^ ω n := by
  rw [← Nat.card_finMulAntidiag_of_squarefree hn, eq_comm]
  apply Finset.card_bij f (f_img hn) f_inj (f_surj hn.ne_zero)

