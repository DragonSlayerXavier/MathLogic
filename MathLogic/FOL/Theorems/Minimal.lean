import MathLogic.FOL.Deduction.Minimal

variable {S : Signature} {α : Type} [BEq α] [MinimalFOLDeduction S α]

-- ==========================================
-- VACUOUS QUANTIFICATION
-- ==========================================

theorem all_vacuous {p : Formula S α} (x : α) : isFreeIn x p = false → ⊢ (∀' x, p) ⇔ p := by
  intro hfree
  have hfwd : ⊢ (∀' x, p) ⇒ p := by
    apply MinimalFOLDeduction.deduction
    exact forall_elim_simple x
  have hbwd : ⊢ p ⇒ (∀' x, p) := by
    let s_ax := MinimalFOLDeduction.dist_imp p (p ⇒ p) p
    let k_ax1 := MinimalFOLDeduction.aff_cons p (p ⇒ p)
    let k_ax2 := MinimalFOLDeduction.aff_cons p p
    let p_imp_p := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp s_ax k_ax1) k_ax2
    exact MinimalFOLDeduction.all_intro x hfree p_imp_p
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∀' x, p) p ) hfwd) hbwd

theorem ex_vacuous {p : Formula S α} (x : α) : isFreeIn x p = false → ⊢ (∃' x, p) ⇔ p := by
  intro hfree
  have hfwd : ⊢ (∃' x, p) ⇒ p := by
    apply MinimalFOLDeduction.ex_elim
    exact hfree
    apply MinimalFOLDeduction.deduction
    intro hp
    exact hp
  have hbwd : ⊢ p ⇒ (∃' x, p) := by
    apply MinimalFOLDeduction.deduction
    exact exists_intro_simple x
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∃' x, p) p ) hfwd) hbwd

-- ==========================================
-- DISTRIBUTION OVER CONJUNCTION
-- ==========================================

theorem all_conj_dist {p q : Formula S α} (x : α) : ⊢ (∀' x, (p ∧ q)) ⇔ (∀' x, p) ∧ (∀' x, q) := by
  have hfwd : ⊢ (∀' x, (p ∧ q)) ⇒ ((∀' x, p) ∧ (∀' x, q)) := by
    apply MinimalFOLDeduction.deduction
    intro h
    let ax_elim := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self (p ∧ q) x)
    have h_elim : ⊢ (∀' x, p ∧ q) ⇒ p ∧ q := by
      rw [MinimalFOLDeduction.subst_self] at ax_elim
      exact ax_elim
    let h_pq := MinimalFOLDeduction.mp h_elim h
    let hp := MinimalFOLDeduction.mp (MinimalFOLDeduction.conj_elim_left p q) h_pq
    let hq := MinimalFOLDeduction.mp (MinimalFOLDeduction.conj_elim_right p q) h_pq
    let h_all_p := MinimalFOLDeduction.mp (MinimalFOLDeduction.all_intro x (by simp [isFreeIn]) (MinimalFOLDeduction.deduction (λ _ => hp))) MinimalFOLDeduction.trivial
    let h_all_q := MinimalFOLDeduction.mp (MinimalFOLDeduction.all_intro x (by simp [isFreeIn]) (MinimalFOLDeduction.deduction (λ _ => hq))) MinimalFOLDeduction.trivial
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.conj_intro (∀' x, p) (∀' x, q)) h_all_p) h_all_q
  have hbwd : ⊢ ((∀' x, p) ∧ (∀' x, q)) ⇒ (∀' x, (p ∧ q)) := by
    apply MinimalFOLDeduction.deduction
    intro h
    have hp := MinimalFOLDeduction.mp (MinimalFOLDeduction.conj_elim_left (∀' x, p) (∀' x, q)) h
    have hq := MinimalFOLDeduction.mp (MinimalFOLDeduction.conj_elim_right (∀' x, p) (∀' x, q)) h
    let ax_p := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self p x)
    let ax_q := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self q x)
    rw [MinimalFOLDeduction.subst_self] at ax_p
    rw [MinimalFOLDeduction.subst_self] at ax_q
    let hp_inst := MinimalFOLDeduction.mp ax_p hp
    let hq_inst := MinimalFOLDeduction.mp ax_q hq
    let hpq_inst := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.conj_intro p q) hp_inst) hq_inst
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.all_intro x (by simp [isFreeIn]) (MinimalFOLDeduction.deduction (λ _ => hpq_inst))) MinimalFOLDeduction.trivial
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro _ _) hfwd) hbwd

theorem ex_conj_dist_left {p q : Formula S α} (x : α) [LawfulBEq α] : isFreeIn x q = false → ⊢ (∃' x, (p ∧ q)) ⇔ (∃' x, p) ∧ q := by
  intro hfree
  have hfwd : ⊢ (∃' x, (p ∧ q)) ⇒ ((∃' x, p) ∧ q) := by
    let h_ex_intro_p := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self p x)
    rw [MinimalFOLDeduction.subst_self] at h_ex_intro_p
    let h_p_exp := imp_trans (MinimalFOLDeduction.conj_elim_left p q) h_ex_intro_p
    let h_p_q := MinimalFOLDeduction.conj_elim_right p q
    let h_p_expq := conj_intro_imp h_p_exp h_p_q
    have h_not_free : isFreeIn x ((∃' x, p) ∧ q) = false := by
      simp only [isFreeIn, BEq.rfl, ↓reduceIte, hfree, Bool.or_self]
    exact MinimalFOLDeduction.ex_elim x h_not_free h_p_expq
  have hbwd : ⊢ ((∃' x, p) ∧ q) ⇒ (∃' x, (p ∧ q)) := by
    apply MinimalFOLDeduction.deduction
    intro h
    let h_exp := MinimalFOLDeduction.mp (MinimalFOLDeduction.conj_elim_left (∃' x, p) q) h
    let h_q := MinimalFOLDeduction.mp (MinimalFOLDeduction.conj_elim_right (∃' x, p) q) h
    let h_p_pq := MinimalFOLDeduction.deduction (λ hp => MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.conj_intro p q) hp) h_q)
    let h_ex_intro_pq := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self (p ∧ q) x)
    rw [MinimalFOLDeduction.subst_self] at h_ex_intro_pq
    let h_p_ex_pq := imp_trans h_p_pq h_ex_intro_pq
    have h_not_free_target : isFreeIn x (∃' x, p ∧ q) = false := by
      simp only [isFreeIn, BEq.rfl, ↓reduceIte]
    let h_ex_elim := MinimalFOLDeduction.ex_elim x h_not_free_target h_p_ex_pq
    exact MinimalFOLDeduction.mp h_ex_elim h_exp
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∃' x, (p ∧ q)) ((∃' x, p) ∧ q)) hfwd) hbwd

-- ==========================================
-- DISTRIBUTION OVER DISJUNCTION
-- ==========================================

theorem all_disj_dist_left {p q : Formula S α} (x : α) [LawfulBEq α] : isFreeIn x q = false → ⊢ (∀' x, (p ∨ q)) ⇔ (∀' x, p) ∨ q := by
  intro hfree
  have hfwd : ⊢ (∀' x, (p ∨ q)) ⇒ ((∀' x, p) ∨ q) := by
    apply MinimalFOLDeduction.deduction
    intro h
    let h_elim := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self (p ∨ q) x)
    rw [MinimalFOLDeduction.subst_self] at h_elim
    let h_pq := MinimalFOLDeduction.mp h_elim h
    let h_p_res := MinimalFOLDeduction.deduction (λ hp =>
      let h_all_p := MinimalFOLDeduction.mp (MinimalFOLDeduction.all_intro x (by unfold isFreeIn; simp) (MinimalFOLDeduction.deduction (λ _ => hp))) MinimalFOLDeduction.trivial
      MinimalFOLDeduction.mp (MinimalFOLDeduction.disj_intro_left (∀' x, p) q) h_all_p)
    let h_q_res := MinimalFOLDeduction.deduction (λ hq =>
      MinimalFOLDeduction.mp (MinimalFOLDeduction.disj_intro_right (∀' x, p) q) hq)
    exact MinimalFOLDeduction.mp (disj_cases h_p_res h_q_res) h_pq
  have hbwd : ⊢ ((∀' x, p) ∨ q) ⇒ (∀' x, (p ∨ q)) := by
    let h_p_pq := MinimalFOLDeduction.deduction (λ hp_all =>
      let h_ax := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self p x)
      let hp_subst := MinimalFOLDeduction.mp h_ax hp_all
      let hp : ⊢ p := MinimalFOLDeduction.subst_self p x ▸ hp_subst
      MinimalFOLDeduction.mp (MinimalFOLDeduction.disj_intro_left p q) hp)
    let h_q_pq := MinimalFOLDeduction.deduction (λ hq =>
      MinimalFOLDeduction.mp (MinimalFOLDeduction.disj_intro_right p q) hq)
    let h_imp := disj_cases h_p_pq h_q_pq
    let h_side : isFreeIn x ((∀' x, p) ∨ q) = false := by
      unfold isFreeIn
      have h_bound : (isFreeIn x (∀' x, p)) = false := by
        unfold isFreeIn
        simp only [BEq.rfl, ↓reduceIte]
      simp only [h_bound, hfree, Bool.or_self]
    exact MinimalFOLDeduction.all_intro x h_side h_imp
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∀' x, (p ∨ q)) ((∀' x, p) ∨ q)) hfwd) hbwd

theorem ex_disj_dist {p q : Formula S α} (x : α) [LawfulBEq α] : ⊢ (∃' x, (p ∨ q)) ⇔ (∃' x, p) ∨ (∃' x, q) := by
  have hfwd : ⊢ (∃' x, (p ∨ q)) ⇒ ((∃' x, p) ∨ (∃' x, q)) := by
    let h_p_ex := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self p x)
    rw [MinimalFOLDeduction.subst_self] at h_p_ex
    let hp_goal := imp_trans h_p_ex (MinimalFOLDeduction.disj_intro_left (∃' x, p) (∃' x, q))

    let h_q_ex := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self q x)
    rw [MinimalFOLDeduction.subst_self] at h_q_ex
    let hq_goal := imp_trans h_q_ex (MinimalFOLDeduction.disj_intro_right (∃' x, p) (∃' x, q))

    let h_cases := disj_cases hp_goal hq_goal
    exact exists_elim x h_cases (by simp [isFreeIn])
  have hbwd : ⊢ ((∃' x, p) ∨ (∃' x, q)) ⇒ (∃' x, (p ∨ q)) := by
    let hp_goal := ex_imp_dist_rule x (MinimalFOLDeduction.disj_intro_left p q)
    let hq_goal := ex_imp_dist_rule x (MinimalFOLDeduction.disj_intro_right p q)
    exact disj_cases hp_goal hq_goal
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∃' x, (p ∨ q)) ((∃' x, p) ∨ (∃' x, q)) ) hfwd) hbwd

-- ==========================================
-- DISTRIBUTION OVER IMPLICATION
-- ==========================================

theorem all_imp_dist_left {p q : Formula S α} (x : α) : isFreeIn x p = false → ⊢ (∀' x, (p ⇒ q)) ⇔ p ⇒ ∀' x, q := by
  intro hfree
  have hfwd : ⊢ (∀' x, (p ⇒ q)) ⇒ (p ⇒ ∀' x, q) := by
    apply MinimalFOLDeduction.deduction
    intro h_all
    let h_pq := forall_elim_simple x h_all
    exact MinimalFOLDeduction.all_intro x hfree h_pq
  have hbwd : ⊢ (p ⇒ ∀' x, q) ⇒ (∀' x, (p ⇒ q)) := by
    apply MinimalFOLDeduction.deduction
    intro h
    let h_elim_ax := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self q x)
    rw [MinimalFOLDeduction.subst_self] at h_elim_ax
    let h_pq := imp_trans h h_elim_ax
    exact rule_gen_simple x h_pq
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∀' x, (p ⇒ q)) (p ⇒ ∀' x, q) ) hfwd) hbwd

theorem ex_imp_dist_left {p q : Formula S α} (x : α) [LawfulBEq α] : isFreeIn x q = false → ⊢ (∃' x, (p ⇒ q)) ⇒ ((∀' x, p) ⇒ q) := by
  intro hfree
  apply MinimalFOLDeduction.deduction
  intro hex_imp

  let h_inner : ⊢ (p ⇒ q) ⇒ ((∀' x, p) ⇒ q) := by
    apply MinimalFOLDeduction.deduction
    intro h_imp
    apply MinimalFOLDeduction.deduction
    intro hall_p
    let h_ax := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self p x)
    rw [MinimalFOLDeduction.subst_self] at h_ax
    let hp := MinimalFOLDeduction.mp h_ax hall_p
    exact MinimalFOLDeduction.mp h_imp hp

  let h_side : isFreeIn x ((∀' x, p) ⇒ q) = false := by
    simp only [isFreeIn, BEq.rfl, ↓reduceIte, hfree, Bool.or_self]

  let h_final_imp := exists_elim x h_inner h_side
  exact MinimalFOLDeduction.mp h_final_imp hex_imp

theorem all_imp_dist_right {p q : Formula S α} (x : α) [LawfulBEq α] : isFreeIn x q = false → ⊢ (∀' x, (p ⇒ q)) ⇔ (∃' x, p) ⇒ q := by
  intro hfree
  have hfwd : ⊢ (∀' x, (p ⇒ q)) ⇒ ((∃' x, p) ⇒ q) := by
    apply MinimalFOLDeduction.deduction
    intro h_all
    let h_ax := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self (p ⇒ q) x)
    rw [MinimalFOLDeduction.subst_self] at h_ax
    let h_actual_imp := MinimalFOLDeduction.mp h_ax h_all
    exact exists_elim x h_actual_imp hfree
  have hbwd : ⊢ ((∃' x, p) ⇒ q) ⇒ (∀' x, (p ⇒ q)) := by
    let h_pq_nested : ⊢ ((∃' x, p) ⇒ q) ⇒ (p ⇒ q) := by
      apply MinimalFOLDeduction.deduction
      intro h_hyp
      apply MinimalFOLDeduction.deduction
      intro hp
      let h_ex_ax := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self p x)
      rw [MinimalFOLDeduction.subst_self] at h_ex_ax
      let h_ex := MinimalFOLDeduction.mp h_ex_ax hp
      exact MinimalFOLDeduction.mp h_hyp h_ex
    let h_side : isFreeIn x ((∃' x, p) ⇒ q) = false := by
      simp [isFreeIn, hfree]
    exact MinimalFOLDeduction.all_intro x h_side h_pq_nested
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∀' x, (p ⇒ q)) ((∃' x, p) ⇒ q) ) hfwd) hbwd

theorem ex_imp_dist_right {p q : Formula S α} (x : α) [LawfulBEq α] : isFreeIn x p = false → ⊢ (∃' x, (p ⇒ q)) ⇒ (p ⇒ (∃' x, q)) := by
  intro h_nf_p

  let h_inner : ⊢ (p ⇒ q) ⇒ (p ⇒ ∃' x, q) := by
    apply MinimalFOLDeduction.deduction
    intro h_pq
    apply MinimalFOLDeduction.deduction
    intro hp
    let h_q := MinimalFOLDeduction.mp h_pq hp
    let h_ex_intro := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self q x)
    rw [MinimalFOLDeduction.subst_self] at h_ex_intro
    exact MinimalFOLDeduction.mp h_ex_intro h_q

  let h_side : isFreeIn x (p ⇒ ∃' x, q) = false := by
    simp only [isFreeIn, BEq.rfl, ↓reduceIte, h_nf_p, Bool.or_false]

  exact exists_elim x h_inner h_side

-- ==========================================
-- NEGATION & DE MORGAN FOR QUANTIFIERS
-- ==========================================

theorem neg_ex_iff_all_neg {p : Formula S α} (x : α) [LawfulBEq α] : ⊢ (¬∃' x, p) ⇔ (∀' x, ¬p) := by
  have hfwd : ⊢ (¬∃' x, p) ⇒ (∀' x, ¬p) := by
    let h_inner_neg : ⊢ (¬∃' x, p) ⇒ ¬p := by
      apply MinimalFOLDeduction.deduction
      intro hnexi
      let h_imp_bot : ⊢ p ⇒ ⊥ := by
        apply MinimalFOLDeduction.deduction
        intro hp
        let h_ex_intro := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self p x)
        rw [MinimalFOLDeduction.subst_self] at h_ex_intro
        let hex := MinimalFOLDeduction.mp h_ex_intro hp
        let h_ex_imp_bot := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim (∃' x, p)) hnexi
        exact MinimalFOLDeduction.mp h_ex_imp_bot hex
      exact MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro p) h_imp_bot

    exact MinimalFOLDeduction.all_intro x (by simp [isFreeIn]) h_inner_neg

  have hbwd : ⊢ (∀' x, ¬p) ⇒ (¬∃' x, p) := by
    apply MinimalFOLDeduction.deduction
    intro hallna
    let h_ex_imp_bot : ⊢ (∃' x, p) ⇒ ⊥ := by
      let h_p_imp_bot : ⊢ p ⇒ ⊥ := by
        apply MinimalFOLDeduction.deduction
        intro hp
        let h_all_elim := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self (¬p) x)
        rw [MinimalFOLDeduction.subst_self] at h_all_elim
        let h_not_p := MinimalFOLDeduction.mp h_all_elim hallna
        let h_p_bot := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim p) h_not_p
        exact MinimalFOLDeduction.mp h_p_bot hp
      exact exists_elim x h_p_imp_bot (by simp [isFreeIn])

    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (∃' x, p)) h_ex_imp_bot

  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (¬∃' x, p) (∀' x, ¬p)) hfwd) hbwd

theorem neg_all_from_ex_neg {p : Formula S α} (x : α) [LawfulBEq α] : ⊢ (∃' x, ¬p) ⇒ ¬∀' x, p := by
  let h_nested : ⊢ (¬p) ⇒ (∀' x, p) ⇒ ⊥ := by
    apply MinimalFOLDeduction.deduction
    intro h_not_p
    apply MinimalFOLDeduction.deduction
    intro h_all_p
    let h_all_ax := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self p x)
    rw [MinimalFOLDeduction.subst_self] at h_all_ax
    let h_p := MinimalFOLDeduction.mp h_all_ax h_all_p
    let h_p_bot := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim p) h_not_p
    exact MinimalFOLDeduction.mp h_p_bot h_p

  let h_ex_elim := exists_elim x h_nested (by simp [isFreeIn])

  apply MinimalFOLDeduction.deduction
  intro h_ex_not_p
  let h_all_p_bot := MinimalFOLDeduction.mp h_ex_elim h_ex_not_p
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (∀' x, p)) h_all_p_bot
