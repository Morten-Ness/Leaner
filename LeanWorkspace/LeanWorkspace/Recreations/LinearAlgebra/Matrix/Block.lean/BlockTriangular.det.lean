import Mathlib

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

