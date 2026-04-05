import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {f : V →ₗ[K] K} {v : V}

theorem exists_basis_of_pairing_eq_zero
    (hfv : f v = 0) (hf : f ≠ 0) (hv : v ≠ 0) :
    ∃ (n : Set V) (b : Basis n K V) (i j : n),
      i ≠ j ∧ v = b i ∧ f = b.coord j := by
  lift v to ker f using hfv
  have : LinearIndepOn K _root_.id {v} := by simpa using hv
  set b₁ : Basis _ K (ker f) := .extend this
  obtain ⟨w, hw⟩ : ∃ w, f w = 1 := by
    simp only [ne_eq, DFunLike.ext_iff, not_forall] at hf
    rcases hf with ⟨w, hw⟩
    use (f w)⁻¹ • w
    simp_all
  set s : Set V := (ker f).subtype '' Set.range b₁
  have hs : span K s = ker f := by
    simp only [s, span_image]
    simp
  have hvs : ↑v ∈ s := by
    refine ⟨v, ?_, by simp⟩
    simp [b₁, Module.Basis.subset_extend this _ _]
  set n := insert w s
  have H₁ : LinearIndepOn K _root_.id n := by
    apply LinearIndepOn.id_insert
    · apply LinearIndepOn.image
      · exact b₁.linearIndependent.linearIndepOn_id
      · simp
    · simp [hs, hw]
  have H₂ : ⊤ ≤ span K n := by
    rintro x -
    simp only [n, mem_span_insert']
    use -f x
    simp [hs, hw]
  set b := Basis.mk H₁ (by simpa using H₂)
  refine ⟨n, b, ⟨v, by simp [n, hvs]⟩, ⟨w, by simp [n]⟩, ?_, by simp [b], ?_⟩
  · apply_fun (f ∘ (↑))
    simp [hw]
  · apply b.ext
    intro i
    rw [Basis.coord_apply, Basis.repr_self]
    simp only [b, Basis.mk_apply]
    rcases i with ⟨x, rfl | ⟨x, hx, rfl⟩⟩
    · simp [hw]
    · suffices x ≠ w by simp [this]
      apply_fun f
      simp [hw]

