import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem splits_mul_iff (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) :
    Polynomial.Splits (f * g) ↔ Polynomial.Splits f ∧ Polynomial.Splits g := by
  refine ⟨fun h ↦ ?_, and_imp.mpr .mul⟩
  generalize hp : f * g = p at *
  generalize hn : p.natDegree = n
  induction n generalizing p f g with
  | zero =>
    rw [← hp, natDegree_mul hf₀ hg₀, Nat.add_eq_zero_iff] at hn
    exact ⟨Polynomial.splits_of_natDegree_eq_zero hn.1, Polynomial.splits_of_natDegree_eq_zero hn.2⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := Polynomial.Splits.exists_eval_eq_zero h (degree_ne_of_natDegree_ne <| hn ▸ by simp)
    have := dvd_iff_isRoot.mpr ha
    rw [← hp, (prime_X_sub_C a).dvd_mul] at this
    wlog hf : X - C a ∣ f with hf2
    · exact .symm <| hf2 n ih hg₀ hf₀ p ((mul_comm g f).trans hp) h hn a ha this.symm <|
        this.resolve_left hf
    obtain ⟨f, rfl⟩ := hf
    rw [mul_assoc] at hp; subst hp
    rw [natDegree_mul (by aesop) (by aesop), natDegree_X_sub_C, add_comm, Nat.succ_inj] at hn
    have := ih (by aesop) hg₀ (f * g) rfl (Polynomial.splits_X_sub_C_mul_iff.mp h) hn
    aesop

