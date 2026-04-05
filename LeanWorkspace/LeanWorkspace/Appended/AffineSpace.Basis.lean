import Mathlib

section

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem affineCombination_coord_eq_self [Fintype ι] (q : P) :
    (Finset.univ.affineCombination k b fun i => b.coord i q) = q := by
  have hq : q ∈ affineSpan k (Set.range b) := by
    rw [AffineBasis.tot b]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  congr
  ext i
  exact AffineBasis.coord_apply_combination_of_mem b (Finset.mem_univ i) hw

end

section

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem coord_apply [DecidableEq ι] (i j : ι) : b.coord i (b j) = if i = j then 1 else 0 := by
  rcases eq_or_ne i j with h | h <;> simp [h]

end

section

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem coord_apply_centroid [CharZero k] (b : AffineBasis ι k P) {s : Finset ι} {i : ι}
    (hi : i ∈ s) : b.coord i (s.centroid k b) = (s.card : k)⁻¹ := by
  rw [Finset.centroid,
    AffineBasis.coord_apply_combination_of_mem b hi (s.sum_centroidWeights_eq_one_of_nonempty _ ⟨i, hi⟩),
    Finset.centroidWeights, Function.const_apply]

end

section

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem coord_apply_combination_of_mem (hi : i ∈ s) {w : ι → k} (hw : s.sum w = 1) :
    b.coord i (s.affineCombination k b w) = w i := by
  classical simp only [AffineBasis.coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_true,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

end

section

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem coord_apply_combination_of_notMem (hi : i ∉ s) {w : ι → k} (hw : s.sum w = 1) :
    b.coord i (s.affineCombination k b w) = 0 := by
  classical simp only [AffineBasis.coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_false,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

end

section

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem coord_reindex (i : ι') : (b.reindex e).coord i = b.coord (e.symm i) := by
  ext
  classical simp [AffineBasis.coord]

end

section

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

variable (k V P)

theorem exists_affineBasis : ∃ (s : Set P) (b : AffineBasis (↥s) k P), ⇑b = ((↑) : s → P) := let ⟨s, _, hs⟩ := AffineBasis.exists_affine_subbasis (AffineSubspace.span_univ k V P)
  ⟨s, hs⟩

end

section

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem exists_affine_subbasis {t : Set P} (ht : affineSpan k t = ⊤) :
    ∃ s ⊆ t, ∃ b : AffineBasis s k P, ⇑b = ((↑) : s → P) := by
  obtain ⟨s, hst, h_tot, h_ind⟩ := exists_affineIndependent k V t
  refine ⟨s, hst, ⟨(↑), h_ind, ?_⟩, rfl⟩
  rw [Subtype.range_coe, h_tot, ht]

end

section

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem ext_elem [Finite ι] {q₁ q₂ : P} (h : ∀ i, b.coord i q₁ = b.coord i q₂) : q₁ = q₂ := by
  cases nonempty_fintype ι
  rw [← AffineBasis.affineCombination_coord_eq_self b q₁, ← AffineBasis.affineCombination_coord_eq_self b q₂]
  simp only [h]

end

section

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem linear_combination_coord_eq_self [Fintype ι] (b : AffineBasis ι k V) (v : V) :
    ∑ i, b.coord i v • b i = v := by
  have hb := AffineBasis.affineCombination_coord_eq_self b v
  rwa [Finset.univ.affineCombination_eq_linear_combination _ _ (AffineBasis.sum_coord_apply_eq_one b v)] at hb

end

section

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem sum_coord_apply_eq_one [Fintype ι] (q : P) : ∑ i, b.coord i q = 1 := by
  have hq : q ∈ affineSpan k (Set.range b) := by
    rw [AffineBasis.tot b]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  convert hw
  exact AffineBasis.coord_apply_combination_of_mem b (Finset.mem_univ _) hw

end

section

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem surjective_coord [Nontrivial ι] (i : ι) : Function.Surjective <| b.coord i := by
  classical
    intro x
    obtain ⟨j, hij⟩ := exists_ne i
    let s : Finset ι := {i, j}
    have hi : i ∈ s := by simp [s]
    let w : ι → k := fun j' => if j' = i then x else 1 - x
    have hw : s.sum w = 1 := by simp [s, w, Finset.sum_ite, Finset.filter_insert, hij,
      Finset.filter_true_of_mem, Finset.filter_false_of_mem]
    use s.affineCombination k b w
    simp [w, AffineBasis.coord_apply_combination_of_mem b hi hw]

end
