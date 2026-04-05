import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_blockDiagonal {o : Type*} [Fintype o] [DecidableEq o] (M : o → Matrix n n R) :
    (blockDiagonal M).det = ∏ k, (M k).det := by
  -- Rewrite the determinants as a sum over permutations.
  simp_rw [Matrix.det_apply']
  -- The right-hand side is a product of sums, rewrite it as a sum of products.
  rw [Finset.prod_sum]
  simp_rw [Finset.prod_attach_univ, Finset.univ_pi_univ]
  -- We claim that the only permutations contributing to the sum are those that
  -- preserve their second component.
  let preserving_snd : Finset (Equiv.Perm (n × o)) := {σ | ∀ x, (σ x).snd = x.snd}
  have mem_preserving_snd :
    ∀ {σ : Equiv.Perm (n × o)}, σ ∈ preserving_snd ↔ ∀ x, (σ x).snd = x.snd := fun {σ} =>
    Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  rw [← Finset.sum_subset (Finset.subset_univ preserving_snd) _]
  -- And that these are in bijection with `o → Equiv.Perm m`.
  · refine (Finset.sum_bij (fun σ _ => prodCongrLeft fun k ↦ σ k (mem_univ k)) ?_ ?_ ?_ ?_).symm
    · intro σ _
      rw [mem_preserving_snd]
      rintro ⟨-, x⟩
      simp only [prodCongrLeft_apply]
    · intro σ _ σ' _ eq
      ext x hx k
      simp only at eq
      have :
        ∀ k x,
          prodCongrLeft (fun k => σ k (Finset.mem_univ _)) (k, x) =
            prodCongrLeft (fun k => σ' k (Finset.mem_univ _)) (k, x) :=
        fun k x => by rw [eq]
      simp only [prodCongrLeft_apply, Prod.mk_inj] at this
      exact (this k x).1
    · intro σ hσ
      rw [mem_preserving_snd] at hσ
      have hσ' x : (σ.symm x).snd = x.snd := by simpa [eq_comm] using hσ (σ.symm x)
      have mk_apply_eq : ∀ k x, ((σ (x, k)).fst, k) = σ (x, k) := by
        intro k x
        ext
        · simp only
        · simp only [hσ]
      have mk_inv_apply_eq : ∀ k x, ((σ.symm (x, k)).fst, k) = σ.symm (x, k) := by grind
      refine ⟨fun k _ => ⟨fun x => (σ (x, k)).fst, fun x => (σ.symm (x, k)).fst, ?_, ?_⟩, ?_, ?_⟩
      · intro x
        simp [mk_apply_eq]
      · intro x
        simp [mk_inv_apply_eq]
      · apply Finset.mem_univ
      · ext ⟨k, x⟩
        · simp only [coe_fn_mk, prodCongrLeft_apply]
        · simp only [prodCongrLeft_apply, hσ]
    · intro σ _
      rw [Finset.prod_mul_distrib, ← Finset.univ_product_univ, Finset.prod_product_right]
      simp only [sign_prodCongrLeft, Units.coe_prod, Int.cast_prod, blockDiagonal_apply_eq,
        prodCongrLeft_apply]
  · intro σ _ hσ
    rw [mem_preserving_snd] at hσ
    obtain ⟨⟨k, x⟩, hkx⟩ := not_forall.mp hσ
    rw [Finset.prod_eq_zero (Finset.mem_univ (k, x)), mul_zero]
    rw [blockDiagonal_apply_ne]
    exact hkx

