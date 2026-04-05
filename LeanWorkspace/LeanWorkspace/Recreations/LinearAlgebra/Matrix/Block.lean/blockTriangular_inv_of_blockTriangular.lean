import Mathlib

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

