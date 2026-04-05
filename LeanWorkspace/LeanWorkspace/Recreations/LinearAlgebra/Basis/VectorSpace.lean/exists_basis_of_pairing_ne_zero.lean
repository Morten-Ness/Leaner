import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {f : V →ₗ[K] K} {v : V}

theorem exists_basis_of_pairing_ne_zero
    (hfv : f v ≠ 0) :
    ∃ (n : Set V) (b : Module.Basis n K V) (i : n),
      v = b i ∧ f = (f v) • b.coord i := by
  set b₁ := Basis.ofVectorSpace K (ker f)
  set s : Set V := (ker f).subtype '' Set.range b₁
  have hs : span K s = ker f := by
    simp only [s, span_image]
    simp
  set n := insert v s
  have H₁ : LinearIndepOn K _root_.id n := by
    apply LinearIndepOn.id_insert
    · apply LinearIndepOn.image
      · exact b₁.linearIndependent.linearIndepOn_id
      · simp
    · simp [hs, hfv]
  have H₂ : ⊤ ≤ span K n := by
    rintro x -
    simp only [n, mem_span_insert']
    use -f x / f v
    simp only [hs, mem_ker, map_add, map_smul, smul_eq_mul]
    field
  set b := Basis.mk H₁ (by simpa using H₂)
  set i : n := ⟨v, s.mem_insert v⟩
  have hi : b i = v := by simp [b, i]
  refine ⟨n, b, i, by simp [b, i], ?_⟩
  rw [← hi]
  apply b.ext
  intro j
  by_cases h : i = j
  · simp [h]
  · suffices f (b j) = 0 by
      simp [Finsupp.single_eq_of_ne h, this]
    rw [← mem_ker, ← hs, Basis.coe_mk]
    apply subset_span
    apply Or.resolve_left (Set.mem_insert_iff.mpr j.prop)
    simp [← hi, b, Subtype.coe_inj, Ne.symm h]

