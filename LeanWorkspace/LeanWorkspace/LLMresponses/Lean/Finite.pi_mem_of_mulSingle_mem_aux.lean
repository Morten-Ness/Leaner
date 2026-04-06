FAIL
import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {η : Type*} {f : η → Type*} [∀ i, Group (f i)]

theorem pi_mem_of_mulSingle_mem_aux [DecidableEq η] (I : Finset η) {H : Subgroup (∀ i, f i)}
    (x : ∀ i, f i) (h1 : ∀ i, i ∉ I → x i = 1) (h2 : ∀ i, i ∈ I → Pi.mulSingle i (x i) ∈ H) :
    x ∈ H := by
  classical
  subst I
  classical
  let F : Finset (∀ i, f i) := I.image (fun i => Pi.mulSingle i (x i))
  have hprod : F.prod id = x := by
    classical
    refine funext ?_
    intro j
    rw [Finset.prod_image]
    · induction I using Finset.induction_on with
      | empty =>
          simp [F]
      | @insert a s ha ih =>
          simp only [Finset.image_insert, ha, Finset.prod_insert, Finset.mem_image, id]
          have hneq : Pi.mulSingle a (x a) j * ∏ x_1 in s.image (fun i => Pi.mulSingle i (x i)), x_1 j = x j := by
            by_cases hja : j = a
            · subst hja
              have hsone : ∀ i ∈ s, Pi.mulSingle i (x i) a = 1 := by
                intro i hi
                simp [Pi.mulSingle, hi, ha]
              simp [hsone, ih]
            · have hmulone : Pi.mulSingle a (x a) j = 1 := by
                simp [Pi.mulSingle, hja]
              have hxs : x j = ∏ x_1 in s.image (fun i => Pi.mulSingle i (x i)), x_1 j := by
                have hjnot : j ∉ insert a s := by
                  intro hjin
                  rw [Finset.mem_insert] at hjin
                  exact hjin.elim hja (h1 j)
                have hxj : x j = 1 := h1 j hjnot
                rw [hxj]
                symmetry
                clear h1 h2
                induction s using Finset.induction_on with
                | empty =>
                    simp
                | @insert b t hbt iht =>
                    simp only [Finset.image_insert, hbt, Finset.prod_insert]
                    have hbja : j ≠ b := by
                      intro hbj
                      subst hbj
                      exact hjnot (by simp)
                    simp [Pi.mulSingle, hbja, iht]
              rw [hmulone, one_mul, hxs]
          exact hneq
    · intro a ha b hb hab
      exact Pi.mulSingle_injective hab
  rw [← hprod]
  refine Subgroup.prod_mem ?_ ?_
  · intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨i, hi, rfl⟩
    exact h2 i hi
  · simp
