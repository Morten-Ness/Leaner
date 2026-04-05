import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [InvolutiveStar α]

theorem IsHermitian.fromBlocks {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} (hA : A.IsHermitian) (hBC : Bᴴ = C) (hD : D.IsHermitian) :
    (A.fromBlocks B C D).IsHermitian := by
  have hCB : Cᴴ = B := by rw [← hBC, conjTranspose_conjTranspose]
  unfold Matrix.IsHermitian
  rw [fromBlocks_conjTranspose, hBC, hCB, hA, hD]

