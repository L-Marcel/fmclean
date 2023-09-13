section propositional

variables P Q R : Prop

------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros p hp,
  exact hp p,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hp,
  by_cases p : P,
  {
    exact p,
  },
  {
    exfalso,
    exact hp p,
  },
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  {
    exact doubleneg_elim P,
  },
  {
    exact doubleneg_intro P,
  }
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pq,
  cases pq with p q,
  {
    right,
    exact p,
  },
  {
    left,
    exact q,
  }
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pq,
  split,
  {
    exact pq.2,
  },
  {
    exact pq.1,
  }
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros npq p,
  cases npq with np q,
  {
    exfalso,
    exact np p,
  },
  {
    exact q,
  }
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros pq np,
  cases pq with p q,
  {
    exfalso,
    exact np p,
  },
  {
    exact q,
  }
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros hpq nq p,
  exact nq (hpq p),
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros h p,
  by_cases q : Q,
  {
    exact q,
  },
  {
    exfalso,
    apply h q,
    exact p,
  },
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  {
    exact impl_as_contrapositive P Q,
  },
  {
    exact impl_as_contrapositive_converse P Q,
  }
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  apply h,
  by_cases p : P,
  {
    left,
    exact p,
  },
  {
    right,
    exact p,
  }
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros pqp np,
  apply np,
  apply pqp,
  intro p,
  exfalso,
  exact np p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros pq npq,
  cases pq with p q,
  {
    exact npq.1 p,
  },
  {
    exact npq.2 q,
  }
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros pq npq,
  cases npq with np nq,
  {
    exact np pq.1,
  },
  {
    exact nq pq.2,
  }
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npq,
  split,
  {
    intro p,
    apply npq,
    left,
    exact p,
  },
  {
    intro q,
    apply npq,
    right,
    exact q,
  }
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros npq pq,
  have n : false := disj_as_negconj P Q pq npq,
  exact n,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro npq,
  by_cases p : P,
  {
    by_cases q : Q,
    {
      exfalso,
      apply npq,
      split,
      {
        exact p,
      },
      {
        exact q,
      }
    },
    {
      left,
      exact q,
    }
  },
  {
    right,
    exact p,
  }
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros h pq,
  cases h with nq np,
  {
    exact nq pq.2,
  },
  {
    exact np pq.1,
  }
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  {
    exact demorgan_conj P Q,
  },
  {
    exact demorgan_conj_converse P Q,
  }
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  {
    exact demorgan_disj P Q,
  },
  {
    exact demorgan_disj_converse P Q,
  }
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  have p : P := h.1,
  have qr : Q ∨ R := h.2,
  cases qr with q r,
  {
    left,
    split,
    {
      exact p,
    },
    {
      exact q,
    },
  },
  {
    right,
    split,
    {
      exact p,
    },
    {
      exact r,
    },
  }
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  cases h with pq pr,
  {
    split,
    {
      exact pq.1,
    },
    {
      left,
      exact pq.2,
    }
  },
  {
    split,
    {
      exact pr.1,
    },
    {
      right,
      exact pr.2,
    }
  }
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  cases h with p qr,
  {
    split,
    {
      left,
      exact p,
    },
    {
      left,
      exact p,
    }
  },
  {
    split,
    {
      right,
      exact qr.1,
    },
    {
      right,
      exact qr.2,
    }
  }
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  have pq : P ∨ Q := h.1,
  have pr : P ∨ R := h.2,
  cases pq with p q,
  {
    left,
    exact p,
  },
  {
    cases pr with p r,
    {
      left,
      exact p,
    },
    {
      right,
      split,
      {
        exact q,
      },
      {
        exact r,
      }
    }
  } 
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros pqr p q,
  apply pqr,
  split,
  {
    exact p,
  },
  {
    exact q,
  }
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros pqr pq,
  have qr : Q → R := pqr pq.1,
  have r : R := qr pq.2,
  exact r,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  exact pq.1,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  exact pq.2,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  {
    exact weaken_conj_right P P,
  },
  {
    intro p,
    split,
    {
      exact p,
    },
    {
      exact p,
    }
  }
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  {
    intro h,
    cases h with p p,
    {
      exact p,
    },
    {
      exact p,
    }
  },
  {
    intro p,
    left,
    exact p,
  }
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intros h u hu,
  apply h,
  existsi u,
  exact hu,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros h hp,
  cases hp with x hx,
  have nhx := h x,
  apply nhx,
  exact hx,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h,
  by_contra hc,
  apply h,
  intro u,
  by_contra hpc,
  apply hc,
  existsi u,
  exact hpc,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros h hp,
  cases h with u npu,
  have pu : P u := hp u,
  exact npu pu,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  {
    exact demorgan_forall U P,
  },
  {
    exact demorgan_forall_converse U P,
  }
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  {
    exact demorgan_exists U P,
  },
  {
    exact demorgan_exists_converse U P,
  }
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros h hp,
  cases h with u hu,
  have nhu : ¬P u := hp u,
  exact nhu hu,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros h hp,
  cases hp with u nhu,
  have hu : P u := h u,
  exact nhu hu,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros h u,
  by_contra hc,
  apply h,
  existsi u,
  exact hc,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h,
  by_contra hc,
  apply h,
  intros u pu,
  apply hc,
  existsi u,
  exact pu,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  {
    exact forall_as_neg_exists U P,
  },
  {
    exact forall_as_neg_exists_converse U P,
  }
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  {
    exact exists_as_neg_forall U P,
  },
  {
    exact exists_as_neg_forall_converse U P,
  }
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with u hu,
  split,
  {
    existsi u,
    exact hu.1,
  },
  {
    existsi u,
    exact hu.2,
  }
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with u hu,
  cases hu with pu qu,
  {
    left,
    existsi u,
    exact pu,
  },
  {
    right,
    existsi u,
    exact qu,
  }
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with pu qu,
  {
    cases pu with u pu,
    existsi u,
    left,
    exact pu,
  },
  {
    cases qu with u qu,
    existsi u,
    right,
    exact qu,
  }
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  {
    intro u,
    have pqu : P u ∧ Q u := h u,
    exact pqu.1
  },
  {
    intro u,
    have pqu : P u ∧ Q u := h u,
    exact pqu.2
  }
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intros h u,
  split,
  {
    have pu : P u := h.1 u,
    exact pu,
  },
  {
    have qu : Q u := h.2 u,
    exact qu,
  }
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intros h u,
  cases h with hp hq,
  {
    left,
    have pu : P u := hp u,
    exact pu,
  },
  {
    right,
    have qu : Q u := hq u,
    exact qu,
  }
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
