import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem eq_centroid_of_forall_mem_median [CharZero k] (s : Affine.Simplex k P n) {hn : 1 < n} {p : P}
    (h : ∀ i, p ∈ s.median i) :
    p = s.centroid := by
  rw [← vsub_eq_zero_iff_eq]
  set i₀ : Fin (n + 1) := 0
  have hp : p = (p -ᵥ s.centroid) +ᵥ s.centroid := by rw [vsub_vadd]
  let s' : Finset (Fin (n + 1)) := {i₀}ᶜ
  let u : s' → V := fun i => s.points i -ᵥ s.centroid
  have h_span : ∀ i : s', p -ᵥ s.centroid ∈ (Submodule.span k ({u i} : Set V)) := by
    intro i
    have hi := h i
    grind only [Affine.Simplex.median_eq_line_point_centroid, vadd_right_mem_affineSpan_pair,
      Submodule.smul_mem, Submodule.mem_span_singleton_self]
  have hi : LinearIndependent k u := by
    set p : Fin (n + 1) → P := fun x => if x = i₀ then s.centroid else s.points x
    have hindep : AffineIndependent k p := by
      have := Affine.Simplex.affineIndependent_points_update_centroid s i₀
      unfold Function.update at this
      grind
    have h1 := (affineIndependent_iff_linearIndependent_vsub k p i₀).mp hindep
    simp_rw [ne_eq, p] at h1
    set f : {x // x ∈ ({i₀}ᶜ : Finset (Fin (n + 1)))} → {x // x ≠ i₀} :=
      have h (x : {x // x ∈ ({i₀}ᶜ : Finset (Fin (n + 1)))}) : x.val ≠ i₀ := by
        grind [mem_compl, Finset.notMem_singleton]
      fun x => ⟨x.val, h x⟩
    have f_inj : Function.Injective f := by intro x y hxy; grind
    have h2 := h1.comp f f_inj
    convert h2 using 1
    grind only [mem_compl, Finset.notMem_singleton]
  have he : ∃ i j : s', i ≠ j := by
    simp only [ne_eq, Subtype.exists, Subtype.mk.injEq, exists_prop]
    have hcard : s'.card = n := by
      rw [Finset.card_compl, Fintype.card_fin, card_singleton, add_tsub_cancel_right]
    have hcard' : 1 < #s' := by grind
    rw [Finset.one_lt_card_iff] at hcard'
    tauto
  choose i j hij using he
  have h_ij : Disjoint ({i} : Set {x // x ∈ s'}) {j} := by simp [hij]
  have h_disjoint : Disjoint (Submodule.span k {u i}) (Submodule.span k {u j}) := by
    simp_rw [← Set.image_singleton, hi.disjoint_span_image h_ij]
  exact Submodule.disjoint_def.1 h_disjoint _ (h_span i) (h_span j)

