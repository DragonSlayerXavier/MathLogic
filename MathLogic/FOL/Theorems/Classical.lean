import MathLogic.FOL.Syntax
import MathLogic.FOL.Deduction.Classical
import MathLogic.FOL.Theorems.Minimal
import MathLogic.FOL.Theorems.Intuitionistic

variable {S : Signature} {α : Type} [BEq α] [ClassicalFOLDeduction S α]

theorem all_iff_not_ex_not {p : Formula S α} (x : α) [LawfulBEq α] : ⊢ (∀' x, p) ⇔ ¬∃' x, ¬p := by
  have hfwd : ⊢ (∀' x, p) ⇒ ¬∃' x, ¬p := by
    let h_inner : ⊢ ¬p ⇒ (∀' x, p) ⇒ ⊥ := by
      apply MinimalFOLDeduction.deduction
      intro h_np
      apply MinimalFOLDeduction.deduction
      intro h_all
      let h_elim := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self p x)
      rw [MinimalFOLDeduction.subst_self] at h_elim
      let h_p := MinimalFOLDeduction.mp h_elim h_all
      let h_p_bot := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim p) h_np
      exact MinimalFOLDeduction.mp h_p_bot h_p
    let h_ex_elim := exists_elim x h_inner (by simp only [isFreeIn, BEq.rfl, ↓reduceIte,
      Bool.or_self])
    apply MinimalFOLDeduction.deduction
    intro h_all
    let h_ex_bot : ⊢ (∃' x, ¬p) ⇒ ⊥ := by
      apply MinimalFOLDeduction.deduction
      intro h_ex
      exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_ex_elim h_ex) h_all
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (∃' x, ¬p)) h_ex_bot
  have hbwd : ⊢ (¬∃' x, ¬p) ⇒ ∀' x, p := by
    let h_p_from_nex : ⊢ (¬∃' x, ¬p) ⇒ p := by
      apply MinimalFOLDeduction.deduction
      intro hnex
      let h_p_bot_bot : ⊢ (p ⇒ ⊥) ⇒ ⊥ := by
        apply MinimalFOLDeduction.deduction
        intro h_p_bot
        let h_np := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro p) h_p_bot
        let h_ex_intro_ax := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self (¬p) x)
        rw [MinimalFOLDeduction.subst_self] at h_ex_intro_ax
        let h_ex_np := MinimalFOLDeduction.mp h_ex_intro_ax h_np
        let h_ex_bot := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim (∃' x, ¬p)) hnex
        exact MinimalFOLDeduction.mp h_ex_bot h_ex_np
      let h_nnp := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (p ⇒ ⊥)) h_p_bot_bot
      let h_nn_p : ⊢ ¬¬p := by
        let h_np_bot : ⊢ ¬p ⇒ ⊥ := by
          apply MinimalFOLDeduction.deduction
          intro h_np_hyp
          let h_p_bot_alt := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim p) h_np_hyp
          exact MinimalFOLDeduction.mp h_p_bot_bot h_p_bot_alt
        exact MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (¬p)) h_np_bot
      exact MinimalFOLDeduction.mp (ClassicalFOLDeduction.dne) h_nn_p
    exact MinimalFOLDeduction.all_intro x (by simp only [isFreeIn, BEq.rfl, ↓reduceIte]) h_p_from_nex
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro _ _) hfwd) hbwd


theorem ex_imp_dist_left_iff {p q : Formula S α} (x : α) [LawfulBEq α] :
  isFreeIn x q = false → ⊢ (∃' x, p ⇒ q) ⇔ (∀' x, p) ⇒ q := by
    intro hfree
    have hfwd : ⊢ (∃' x, p ⇒ q) ⇒ ((∀' x, p) ⇒ q) := by
      let h_inner : ⊢ (p ⇒ q) ⇒ ((∀' x, p) ⇒ q) := by
        apply MinimalFOLDeduction.deduction
        intro hpq
        apply MinimalFOLDeduction.deduction
        intro hallp
        let h_all_elim_ax := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self p x)
        rw [MinimalFOLDeduction.subst_self] at h_all_elim_ax
        let h_p := MinimalFOLDeduction.mp h_all_elim_ax hallp
        exact MinimalFOLDeduction.mp hpq h_p
      apply MinimalFOLDeduction.deduction
      intro hex
      let h_ex_elim := exists_elim x h_inner (by simp only [isFreeIn, BEq.rfl, ↓reduceIte, hfree,
        Bool.or_self])
      exact MinimalFOLDeduction.mp h_ex_elim hex
    have hbwd : ⊢ ((∀' x, p) ⇒ q) ⇒ (∃' x, p ⇒ q) := by
      apply MinimalFOLDeduction.deduction
      intro h_hyp
      let h_nn_goal_bot : ⊢ ¬(∃' x, p ⇒ q) ⇒ ⊥ := by
        apply MinimalFOLDeduction.deduction
        intro h_neg_ex
        let h_neg_ex_imp_bot := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim (∃' x, p ⇒ q)) h_neg_ex


        let h_all_p : ⊢ ∀' x, p := by
          let h_p_raw : ⊢ ¬(∃' x, p ⇒ q) ⇒ p := by
            apply MinimalFOLDeduction.deduction
            intro h_nex
            let h_nex_imp_bot_inner := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim (∃' x, p ⇒ q)) h_nex
            let h_p_bot_bot : ⊢ ¬p ⇒ ⊥ := by
              apply MinimalFOLDeduction.deduction
              intro h_np
              let h_p_bot := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim p) h_np
              let h_pq : ⊢ p ⇒ q := by
                apply MinimalFOLDeduction.deduction
                intro hp

                exact MinimalFOLDeduction.mp (ex_falso) (MinimalFOLDeduction.mp h_p_bot hp)
              let h_ex_intro_ax := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self (p ⇒ q) x)
              rw [MinimalFOLDeduction.subst_self] at h_ex_intro_ax

              exact MinimalFOLDeduction.mp h_nex_imp_bot_inner (MinimalFOLDeduction.mp h_ex_intro_ax h_pq)
            let h_nn_p := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (¬p)) h_p_bot_bot
            exact MinimalFOLDeduction.mp (ClassicalFOLDeduction.dne) h_nn_p


          let h_gen_all := MinimalFOLDeduction.all_intro x (by simp only [isFreeIn, BEq.rfl,
            ↓reduceIte]) h_p_raw
          exact MinimalFOLDeduction.mp h_gen_all h_neg_ex


        let h_q := MinimalFOLDeduction.mp h_hyp h_all_p


        let h_neg_q : ⊢ q ⇒ ⊥ := by
          apply MinimalFOLDeduction.deduction
          intro h_val_q
          let h_pq : ⊢ p ⇒ q := MinimalFOLDeduction.deduction (λ _ => h_val_q)
          let h_ex_intro_ax := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self (p ⇒ q) x)
          rw [MinimalFOLDeduction.subst_self] at h_ex_intro_ax
          exact MinimalFOLDeduction.mp h_neg_ex_imp_bot (MinimalFOLDeduction.mp h_ex_intro_ax h_pq)

        exact MinimalFOLDeduction.mp h_neg_q h_q


      let h_n_n_ex := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (¬(∃' x, p ⇒ q))) h_nn_goal_bot
      exact MinimalFOLDeduction.mp (ClassicalFOLDeduction.dne) h_n_n_ex
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro _ _) hfwd) hbwd


theorem ex_imp_dist_right_iff {p q : Formula S α} (x : α) [LawfulBEq α] :
  isFreeIn x p = false → ⊢ (∃' x, p ⇒ q) ⇔ p ⇒ ∃' x, q := by
    intro hfree
    have hfwd : ⊢ (∃' x, p ⇒ q) ⇒ (p ⇒ ∃' x, q) := by
      let h_inner : ⊢ (p ⇒ q) ⇒ (p ⇒ ∃' x, q) := by
        apply MinimalFOLDeduction.deduction
        intro hpq
        apply MinimalFOLDeduction.deduction
        intro hp
        let hq := MinimalFOLDeduction.mp hpq hp
        let hex_intro_ax := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self q x)
        rw [MinimalFOLDeduction.subst_self] at hex_intro_ax
        exact MinimalFOLDeduction.mp hex_intro_ax hq
      apply MinimalFOLDeduction.deduction
      intro hex_pq
      let h_ex_elim := exists_elim x h_inner (by simp only [isFreeIn, BEq.rfl, ↓reduceIte, hfree,
        Bool.or_self])
      exact MinimalFOLDeduction.mp h_ex_elim hex_pq
    have hbwd : ⊢ (p ⇒ ∃' x, q) ⇒ (∃' x, p ⇒ q) := by
      apply MinimalFOLDeduction.deduction
      intro h_hyp
      let h_nn_goal_bot : ⊢ ¬(∃' x, p ⇒ q) ⇒ ⊥ := by
        apply MinimalFOLDeduction.deduction
        intro h_neg_ex
        let h_neg_ex_imp_bot := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim (∃' x, p ⇒ q)) h_neg_ex
        let h_p : ⊢ p := by
          let h_p_bot_bot : ⊢ ¬p ⇒ ⊥ := by
            apply MinimalFOLDeduction.deduction
            intro h_np
            let h_p_bot := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim p) h_np
            let h_pq : ⊢ p ⇒ q := by
              apply MinimalFOLDeduction.deduction
              intro hp
              exact MinimalFOLDeduction.mp (ex_falso) (MinimalFOLDeduction.mp h_p_bot hp)
            let h_ex_intro_ax := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self (p ⇒ q) x)
            rw [MinimalFOLDeduction.subst_self] at h_ex_intro_ax
            exact MinimalFOLDeduction.mp h_neg_ex_imp_bot (MinimalFOLDeduction.mp h_ex_intro_ax h_pq)
          let h_nn_p := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (¬p)) h_p_bot_bot
          exact MinimalFOLDeduction.mp (ClassicalFOLDeduction.dne) h_nn_p
        let h_ex_q := MinimalFOLDeduction.mp h_hyp h_p
        let h_neg_ex_q : ⊢ (∃' x, q) ⇒ ⊥ := by
          let h_q_bot : ⊢ q ⇒ ⊥ := by
            apply MinimalFOLDeduction.deduction
            intro h_val_q
            let h_pq : ⊢ p ⇒ q := MinimalFOLDeduction.deduction (λ _ => h_val_q)
            let h_ex_intro_ax := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self (p ⇒ q) x)
            rw [MinimalFOLDeduction.subst_self] at h_ex_intro_ax
            exact MinimalFOLDeduction.mp h_neg_ex_imp_bot (MinimalFOLDeduction.mp h_ex_intro_ax h_pq)
          exact MinimalFOLDeduction.ex_elim x (by simp only [isFreeIn]) h_q_bot
        exact MinimalFOLDeduction.mp h_neg_ex_q h_ex_q
      let h_n_n_ex := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (¬(∃' x, p ⇒ q))) h_nn_goal_bot
      exact MinimalFOLDeduction.mp (ClassicalFOLDeduction.dne) h_n_n_ex
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro _ _) hfwd) hbwd



theorem ex_not_iff_not_all {p : Formula S α} (x : α) [LawfulBEq α] :
  ⊢ (∃' x, ¬p) ⇔ ¬∀' x, p := by
  have hfwd : ⊢ (∃' x, ¬p) ⇒ ¬∀' x, p := by
    let h_inner : ⊢ ¬p ⇒ (∀' x, p) ⇒ ⊥ := by
      apply MinimalFOLDeduction.deduction
      intro h_np
      apply MinimalFOLDeduction.deduction
      intro h_all
      let h_elim_ax := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self p x)
      rw [MinimalFOLDeduction.subst_self] at h_elim_ax
      let h_p := MinimalFOLDeduction.mp h_elim_ax h_all
      let h_p_bot := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim p) h_np
      exact MinimalFOLDeduction.mp h_p_bot h_p
    let h_ex_elim := MinimalFOLDeduction.ex_elim x (by simp only [isFreeIn, BEq.rfl, ↓reduceIte,
      Bool.or_self]) h_inner
    apply MinimalFOLDeduction.deduction
    intro h_ex
    let h_all_bot := MinimalFOLDeduction.mp h_ex_elim h_ex
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (∀' x, p)) h_all_bot
  have hbwd : ⊢ (¬∀' x, p) ⇒ (∃' x, ¬p) := by
    apply MinimalFOLDeduction.deduction
    intro h_not_all
    let h_nn_goal_bot : ⊢ ¬(∃' x, ¬p) ⇒ ⊥ := by
      apply MinimalFOLDeduction.deduction
      intro h_not_ex_not
      let h_not_ex_not_imp_bot := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim (∃' x, ¬p)) h_not_ex_not
      let h_all_p : ⊢ ∀' x, p := by
        let h_p_raw : ⊢ ¬(∃' x, ¬p) ⇒ p := by
          apply MinimalFOLDeduction.deduction
          intro h_nex
          let h_nex_imp_bot_inner := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim (∃' x, ¬p)) h_nex
          let h_p_bot_bot : ⊢ ¬p ⇒ ⊥ := by
            apply MinimalFOLDeduction.deduction
            intro h_np
            let h_ex_intro_ax := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self (¬p) x)
            rw [MinimalFOLDeduction.subst_self] at h_ex_intro_ax
            exact MinimalFOLDeduction.mp h_nex_imp_bot_inner (MinimalFOLDeduction.mp h_ex_intro_ax h_np)
          let h_nn_p := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (¬p)) h_p_bot_bot
          exact MinimalFOLDeduction.mp (ClassicalFOLDeduction.dne) h_nn_p
        let h_gen := MinimalFOLDeduction.all_intro x (by simp only [isFreeIn, BEq.rfl, ↓reduceIte]) h_p_raw
        exact MinimalFOLDeduction.mp h_gen h_not_ex_not
      let h_all_bot := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim (∀' x, p)) h_not_all
      exact MinimalFOLDeduction.mp h_all_bot h_all_p
    let h_n_n_ex := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (¬(∃' x, ¬p))) h_nn_goal_bot
    exact MinimalFOLDeduction.mp (ClassicalFOLDeduction.dne) h_n_n_ex
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro _ _) hfwd) hbwd
