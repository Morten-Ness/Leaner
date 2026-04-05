import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable (P Q : ChainComplex V ℕ) (zero : P.X 0 ⟶ Q.X 0) (one : P.X 1 ⟶ Q.X 1)
  (one_zero_comm : one ≫ Q.d 1 0 = P.d 1 0 ≫ zero)
  (succ :
    ∀ (n : ℕ)
      (p :
        Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
          f' ≫ Q.d (n + 1) n = P.d (n + 1) n ≫ f),
      Σ' f'' : P.X (n + 2) ⟶ Q.X (n + 2), f'' ≫ Q.d (n + 2) (n + 1) = P.d (n + 2) (n + 1) ≫ p.2.1)

theorem mkHom_f_succ_succ (n : ℕ) :
    (ChainComplex.mkHom P Q HomologicalComplex.zero one one_zero_comm succ).f (n + 2) =
      (succ n
          ⟨(ChainComplex.mkHom P Q HomologicalComplex.zero one one_zero_comm succ).f n,
            (ChainComplex.mkHom P Q HomologicalComplex.zero one one_zero_comm succ).f (n + 1),
            (ChainComplex.mkHom P Q HomologicalComplex.zero one one_zero_comm succ).comm (n + 1) n⟩).1 := by
  dsimp [ChainComplex.mkHom, ChainComplex.mkHomAux]

