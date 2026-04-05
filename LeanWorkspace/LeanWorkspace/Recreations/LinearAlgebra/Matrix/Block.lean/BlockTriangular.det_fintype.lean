import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem BlockTriangular.det_fintype [DecidableEq α] [Fintype α] [LinearOrder α]
    (h : Matrix.BlockTriangular M b) : M.det = ∏ k : α, (M.toSquareBlock b k).det := by
  refine h.det.trans (prod_subset (subset_univ _) fun a _ ha => ?_)
  have : IsEmpty { i // b i = a } := ⟨fun i => ha <| mem_image.2 ⟨i, mem_univ _, i.2⟩⟩
  exact det_isEmpty

