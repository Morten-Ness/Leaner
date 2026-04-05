import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem twoBlockTriangular_det (M : Matrix m m R) (p : m → Prop) [DecidablePred p]
    (h : ∀ i, ¬p i → ∀ j, p j → M i j = 0) :
    M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det := by
  rw [Matrix.det_toBlock M p]
  convert det_fromBlocks_zero₂₁ (toBlock M p p) (toBlock M p fun j => ¬p j)
      (toBlock M (fun j => ¬p j) fun j => ¬p j)
  ext i j
  exact h (↑i) i.2 (↑j) j.2

