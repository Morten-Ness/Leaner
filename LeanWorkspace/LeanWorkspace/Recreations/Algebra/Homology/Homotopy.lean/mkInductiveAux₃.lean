import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

variable {P Q : ChainComplex V ℕ}

variable (e : P ⟶ Q) (zero : P.X 0 ⟶ Q.X 1) (comm_zero : e.f 0 = zero ≫ Q.d 1 0)
  (one : P.X 1 ⟶ Q.X 2) (comm_one : e.f 1 = P.d 1 0 ≫ zero + one ≫ Q.d 2 1)
  (succ :
    ∀ (n : ℕ)
      (p :
        Σ' (f : P.X n ⟶ Q.X (n + 1)) (f' : P.X (n + 1) ⟶ Q.X (n + 2)),
          e.f (n + 1) = P.d (n + 1) n ≫ f + f' ≫ Q.d (n + 2) (n + 1)),
      Σ' f'' : P.X (n + 2) ⟶ Q.X (n + 3),
        e.f (n + 2) = P.d (n + 2) (n + 1) ≫ p.2.1 + f'' ≫ Q.d (n + 3) (n + 2))

theorem mkInductiveAux₃ (i j : ℕ) (h : i + 1 = j) :
    (Homotopy.mkInductiveAux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.xPrevIso h).hom =
      (P.xNextIso h).inv ≫ (Homotopy.mkInductiveAux₂ e zero comm_zero one comm_one succ j).1 := by
  subst j
  rcases i with (_ | _ | i) <;> simp [Homotopy.mkInductiveAux₂]

