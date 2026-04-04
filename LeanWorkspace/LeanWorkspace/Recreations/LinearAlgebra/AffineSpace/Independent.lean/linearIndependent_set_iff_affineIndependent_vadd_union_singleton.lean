import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

theorem linearIndependent_set_iff_affineIndependent_vadd_union_singleton {s : Set V}
    (hs : ∀ v ∈ s, v ≠ (0 : V)) (p₁ : P) : LinearIndependent k (fun v => v : s → V) ↔
    AffineIndependent k (fun p => p : ({p₁} ∪ (fun v => v +ᵥ p₁) '' s : Set P) → P) := by
  rw [affineIndependent_set_iff_linearIndependent_vsub k
      (Set.mem_union_left _ (Set.mem_singleton p₁))]
  have h : (fun p => (p -ᵥ p₁ : V)) '' (({p₁} ∪ (fun v => v +ᵥ p₁) '' s) \ {p₁}) = s := by
    simp_rw [Set.union_diff_left, Set.image_diff (vsub_left_injective p₁), Set.image_image,
      Set.image_singleton, vsub_self, vadd_vsub, Set.image_id']
    exact Set.diff_singleton_eq_self fun h => hs 0 h rfl
  rw [h]

