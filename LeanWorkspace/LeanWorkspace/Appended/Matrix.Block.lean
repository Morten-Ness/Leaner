import Mathlib

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

theorem BlockTriangular.add [AddZeroClass R] (hM : Matrix.BlockTriangular M b) (hN : Matrix.BlockTriangular N b) :
    Matrix.BlockTriangular (M + N) b := fun i j h => by simp_rw [Matrix.add_apply, hM h, hN h, zero_add]

end

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

theorem BlockTriangular.add_iff_left [AddGroup R] (hN : Matrix.BlockTriangular N b) :
    Matrix.BlockTriangular (M + N) b ↔ Matrix.BlockTriangular M b := ⟨(by simpa using ·.sub hN), (·.add hN)⟩

end

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

theorem BlockTriangular.add_iff_right [AddGroup R] (hM : Matrix.BlockTriangular M b) :
    Matrix.BlockTriangular (M + N) b ↔ Matrix.BlockTriangular N b := ⟨(by simpa using hM.neg.add ·), hM.add⟩

end

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem BlockTriangular.det [DecidableEq α] [LinearOrder α] (hM : Matrix.BlockTriangular M b) :
    M.det = ∏ a ∈ Finset.univ.image b, (M.toSquareBlock b a).det := by
  suffices ∀ hs : Finset α, Finset.univ.image b = hs → M.det = ∏ a ∈ hs, (M.toSquareBlock b a).det by
    exact this _ rfl
  intro s hs
  induction s using Finset.eraseInduction generalizing m with | H s ih =>
  subst hs
  cases isEmpty_or_nonempty m
  · simp
  let k := (Finset.univ.image b).max' (univ_nonempty.image _)
  rw [Matrix.twoBlockTriangular_det' M fun i => b i = k]
  · have : Finset.univ.image b = insert k ((Finset.univ.image b).erase k) := by
      rw [insert_erase]
      apply max'_mem
    rw [this, prod_insert (notMem_erase _ _)]
    refine congr_arg _ ?_
    let b' := fun i : { a // b a ≠ k } => b ↑i
    have h' : Matrix.BlockTriangular (M.toSquareBlockProp fun i => b i ≠ k) b' := hM.submatrix
    have hb' : image b' Finset.univ = (image b Finset.univ).erase k := by
      convert image_subtype_ne_univ_eq_image_erase k b
    rw [ih _ (max'_mem _ _) h' hb']
    refine Finset.prod_congr rfl fun l hl => ?_
    let he : { a // b' a = l } ≃ { a // b a = l } :=
      haveI hc : ∀ i, b i = l → b i ≠ k := fun i hi => ne_of_eq_of_ne hi (ne_of_mem_erase hl)
      Equiv.subtypeSubtypeEquivSubtype @hc
    simp only [toSquareBlock_def]
    erw [← Matrix.det_reindex_self he.symm fun i j : { a // b a = l } => M ↑i ↑j]
    rfl
  · intro i hi j hj
    apply hM
    rw [hi]
    apply lt_of_le_of_ne _ hj
    exact Finset.le_max' (Finset.univ.image b) _ (mem_image_of_mem _ (mem_univ _))

end

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem BlockTriangular.inv_toBlock [LinearOrder α] [Invertible M] (hM : Matrix.BlockTriangular M b)
    (k : α) :
    (M.toBlock (fun i => b i < k) fun i => b i < k)⁻¹ =
      M⁻¹.toBlock (fun i => b i < k) fun i => b i < k := inv_eq_left_inv <| hM.toBlock_inverse_mul_toBlock_eq_one k

end

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LinearOrder α]

theorem BlockTriangular.mul [Fintype m] [NonUnitalNonAssocSemiring R]
    {M N : Matrix m m R} (hM : Matrix.BlockTriangular M b)
    (hN : Matrix.BlockTriangular N b) : Matrix.BlockTriangular (M * N) b := by
  intro i j hij
  apply Finset.sum_eq_zero
  intro k _
  by_cases! hki : b k < b i
  · simp_rw [hM hki, zero_mul]
  · simp_rw [hN (lt_of_lt_of_le hij hki), mul_zero]

end

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

theorem BlockTriangular.sub [SubNegZeroMonoid R]
    (hM : Matrix.BlockTriangular M b) (hN : Matrix.BlockTriangular N b) :
    Matrix.BlockTriangular (M - N) b := fun i j h => by simp_rw [Matrix.sub_apply, hM h, hN h, sub_zero]

end

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

theorem BlockTriangular.sub_iff_left [AddGroup R] (hN : Matrix.BlockTriangular N b) :
    Matrix.BlockTriangular (M - N) b ↔ Matrix.BlockTriangular M b := ⟨(by simpa using ·.add hN), (·.sub hN)⟩

end

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

theorem BlockTriangular.sub_iff_right [AddGroup R] (hM : Matrix.BlockTriangular M b) :
    Matrix.BlockTriangular (M - N) b ↔ Matrix.BlockTriangular N b := ⟨(by simpa using ·.neg.add hM), hM.sub⟩

end

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem BlockTriangular.toBlock_inverse_mul_toBlock_eq_one [LinearOrder α] [Invertible M]
    (hM : Matrix.BlockTriangular M b) (k : α) :
    ((M⁻¹.toBlock (fun i => b i < k) fun i => b i < k) *
        M.toBlock (fun i => b i < k) fun i => b i < k) =
      1 := by
  let p i := b i < k
  have h_sum :
    M⁻¹.toBlock p p * M.toBlock p p +
        (M⁻¹.toBlock p fun i => ¬p i) * M.toBlock (fun i => ¬p i) p =
      1 := by
    rw [← toBlock_mul_eq_add, inv_mul_of_invertible M, toBlock_one_self]
  have h_zero : M.toBlock (fun i => ¬p i) p = 0 := by
    ext i j
    simpa using hM (lt_of_lt_of_le j.2 (le_of_not_gt i.2))
  simpa [h_zero] using h_sum

end

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem blockTriangular_inv_of_blockTriangular [LinearOrder α] [Invertible M]
    (hM : Matrix.BlockTriangular M b) : Matrix.BlockTriangular M⁻¹ b := by
  suffices ∀ hs : Finset α, Finset.univ.image b = hs → Matrix.BlockTriangular M⁻¹ b by exact this _ rfl
  intro s hs
  induction s using Finset.strongInduction generalizing m with | H s ih =>
  subst hs
  intro i j hij
  haveI : Inhabited m := ⟨i⟩
  let k := (Finset.univ.image b).max' (univ_nonempty.image _)
  let b' := fun i : { a // b a < k } => b ↑i
  let A := M.toBlock (fun i => b i < k) fun j => b j < k
  obtain hbi | hi : b i = k ∨ _ := (le_max' _ (b i) <| mem_image_of_mem _ <| mem_univ _).eq_or_lt
  · have : M⁻¹.toBlock (fun i => k ≤ b i) (fun i => b i < k) ⟨i, hbi.ge⟩ ⟨j, hbi ▸ hij⟩ = 0 := by
      simp only [Matrix.toBlock_inverse_eq_zero hM k, Matrix.zero_apply]
    simp [this.symm]
  haveI : Invertible A := hM.invertibleToBlock _
  have hA : A.BlockTriangular b' := hM.submatrix
  have hb' : image b' Finset.univ ⊂ image b Finset.univ := by
    convert image_subtype_univ_ssubset_image_univ k b _ (fun a => a < k) (lt_irrefl _)
    convert max'_mem (α := α) _ _
  have hij' : b' ⟨j, hij.trans hi⟩ < b' ⟨i, hi⟩ := by simp_rw [b', hij]
  simp [A, hM.inv_toBlock k, (ih (image b' Finset.univ) hb' hA rfl hij').symm]

end

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem det_toSquareBlock_id (M : Matrix m m R) (i : m) : (M.toSquareBlock id i).det = M i i := letI : Unique { a // id a = i } := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  (det_unique _).trans rfl

end

section

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem matrixOfPolynomials_blockTriangular {R} [Semiring R] {n : ℕ} (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree ≤ i) :
    Matrix.BlockTriangular (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) id := fun _ j h => by
    exact coeff_eq_zero_of_natDegree_lt <| Nat.lt_of_le_of_lt (h_deg j) h

end
