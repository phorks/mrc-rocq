From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Strings.String.
From stdpp Require Import base gmap.
From Equations Require Import Equations.
From MRC Require Import Prelude.
From MRC Require Import Stdppp.
From MRC Require Import SeqNotation.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.

Open Scope stdpp_scope.
Open Scope refiney_scope.

Section syntax.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation sgn := (model_sgn M).

  Local Notation term := (term M).
  Local Notation formula := (formula M).
  Local Notation final_term := (final_term M).
  Local Notation final_formula := (final_formula M).

  Unset Elimination Schemes.
  Inductive prog : Type :=
  | PAsgn (xs : list final_variable) (ts: list final_term) `{!OfSameLength xs ts}
  | PSeq (p1 p2 : prog)
  | PIf (gcs : list (final_formula * prog))
  | PWhile (g inv : final_formula) (variant : final_term) (p : prog)
  | PSpec (w : list final_variable) (pre : final_formula) (post : formula)
  | PVar (x : final_variable) (ty : value_ty) (p : prog)
  | PConst (x : final_variable) (ty : value_ty) (p : prog).
  Set Elimination Schemes.

  Fixpoint prog_ind P :
    (∀ xs ts H, P (@PAsgn xs ts H)) →
    (∀ p1 p2, P p1 → P p2 → P (PSeq p1 p2)) →
    (∀ gcs, Forall (λ fp, P fp.2) gcs → P (PIf gcs)) →
    (∀ g inv v p, P p → P (PWhile g inv v p)) →
    (∀ w pre post, P (PSpec w pre post)) →
    (∀ x ty p, P p → P (PVar x ty p)) →
    (∀ x ty p, P p → P (PConst x ty p)) →
    ∀ p, P p.
  Proof with auto.
    intros Hasgn Hseq Hif Hwhile Hspec Hvar Hcons. destruct p.
    - apply Hasgn.
    - apply Hseq; apply prog_ind...
    - apply Hif. induction gcs... constructor... apply prog_ind...
    - apply Hwhile. apply prog_ind...
    - apply Hspec.
    - apply Hvar. apply prog_ind...
    - apply Hcons. apply prog_ind...
  Qed.

  Fixpoint PVarList (xs : list final_variable) (ty : value_ty) (p : prog) :=
    match xs with
    | [] => p
    | x :: xs => PVar x ty (PVarList xs ty p)
    end.

  Fixpoint PConstList (xs : list final_variable) (ty : value_ty) (p : prog) :=
    match xs with
    | [] => p
    | x :: xs => PConst x ty (PConstList xs ty p)
    end.

  Notation gcmd_list := (list (final_formula * prog)).
  Definition gcmd_comprehension (gs : list final_formula) (f : final_formula → prog) : gcmd_list :=
    map (λ A, (A, f A)) gs.

  Fixpoint modified_final_vars p : gset final_variable :=
    match p with
    | PAsgn xs ts => list_to_set xs
    | PSeq p1 p2 => modified_final_vars p1 ∪ modified_final_vars p2
    | PIf gcs => ⋃ ((modified_final_vars ∘ snd) <$> gcs)
    | PWhile _ _ _ p => modified_final_vars p
    | PSpec w pre post => list_to_set w
    | PVar x _ p => modified_final_vars p ∖ {[x]}
    | PConst x _ p => modified_final_vars p ∖ {[x]}
    end.

  Definition modified_vars p : gset variable := as_var_set (modified_final_vars p).
  Notation "'Δ' p" := (modified_vars p) (at level 50).

  Fixpoint prog_fvars p : gset variable :=
    match p with
    | PAsgn xs ts => (list_to_set (as_var <$> xs)) ∪ ⋃ (term_fvars ∘ as_term <$> ts)
    | PSeq p1 p2 => prog_fvars p1 ∪ prog_fvars p2
    | PIf gcs => ⋃ ((λ gcmd, prog_fvars (snd gcmd) ∪
                                 formula_fvars (as_formula (fst gcmd))) <$> gcs)
    | PWhile g inv v p => formula_fvars g ∪ formula_fvars inv ∪ term_fvars v ∪ prog_fvars p
    | PSpec w pre post =>
        (list_to_set (as_var_F w) ∪
        formula_fvars pre ∪
        (formula_fvars post ∖ (list_to_set (initial_fvars post))) ∪
        list_to_set (as_var_F (finalized_initial_fvars post)))
    | PVar x _ p => prog_fvars p ∖ {[as_var x]}
    | PConst x _ p => prog_fvars p ∖ {[as_var x]}
  end.

  Lemma modified_vars_subseteq_fvars {p : prog} :
    Δ p ⊆ prog_fvars p.
  Proof.
    unfold modified_vars. induction p.
    - simpl. simpl. induction_same_length xs ts as x t.
      + simpl. unfold as_var_set. set_solver.
      + simpl. unfold as_var_set. rewrite set_map_union. apply union_subseteq. split.
        * rewrite set_map_singleton. set_solver.
        * set_solver.
    - simpl. unfold as_var_set. set_solver.
    - simpl. unfold as_var_set. induction gcs.
      + simpl. set_solver.
      + simpl in *. rewrite set_map_union. apply union_subseteq. split.
        * apply union_subseteq_l'. inversion H. subst. etrans; [exact H2|set_solver].
        * apply union_subseteq_r'. etrans.
          -- apply IHgcs... inversion H. set_solver.
          -- set_solver.
    - simpl. unfold as_var_set. set_solver.
    - unfold as_var_set. simpl. do 3 apply union_subseteq_l'. induction w; set_solver.
    - simpl. set_solver.
    - simpl. set_solver.
  Qed.

  Fixpoint any_guard (gcs : gcmd_list) : formula :=
    match gcs with
    | [] => <! true !>
    | (g, _)::cmds => <! g ∨ $(any_guard cmds) !>
    end.

  Fixpoint all_cmds (gcs : gcmd_list) (A : formula) : formula :=
    match gcs with
    | [] => <! true !>
    | (g, _)::cmds => <! (g ⇔ A) ∧ $(all_cmds cmds A) !>
    end.

  (* ******************************************************************* *)
  (* some extreme programs                                               *)
  (* ******************************************************************* *)

  Definition abort := PSpec [] <!! false !!> <! true !>.
  Definition abort_w w := PSpec w <!! false !!> <! true !>.
  Definition choose_w w := PSpec w <!! true !!> <! true !>.
  Definition skip := PSpec [] <!! true !!> <! true !>.
  Definition magic := PSpec [] <!! true !!> <! false !>.
  Definition magic_w w := PSpec w <!! true !!> <! false !>.

  (* ******************************************************************* *)
  (* subst and rank induction                                            *)
  (* ******************************************************************* *)

  Fixpoint prog_rank (p : prog) : nat :=
    match p with
    | PAsgn xs ts => 0
    | PSeq p1 p2 => 1 + max (prog_rank p1) (prog_rank p2)
    | PIf gcs => 1 + max_list_with (prog_rank ∘ snd) gcs
    | PWhile _ _ _ p => 1 + prog_rank p
    | PSpec w pre post => 0
    | PVar x _ p => 1 + prog_rank p
    | PConst x _ p => 1 + prog_rank p
    end.

  Fixpoint subst_prog p (x x' : final_variable) :=
    match p with
    | PAsgn xs ts => PAsgn
                       ((λ y, if (decide (y = x)) then x' else y) <$> xs)
                       ((λ (t : final_term), as_final_term (subst_term t x (TVar x'))) <$> ts)
    | PSeq p1 p2 => PSeq (subst_prog p1 x x') (subst_prog p2 x x')
    | PIf gcs => PIf ((λ gc : final_formula * prog,
                          (as_final_formula (subst_formula gc.1 x (TVar x')),
                            subst_prog gc.2 x x')) <$> gcs)
    | PWhile g inv v p => PWhile
                            (as_final_formula $ subst_formula g x (TVar x'))
                            (as_final_formula $ subst_formula inv x (TVar x'))
                            (as_final_term    $ subst_term v x (TVar x'))
                            (subst_prog p x x')
    | PSpec w pre post => PSpec
                            ((λ y, if (decide (y = x)) then x' else y) <$> w)
                            (as_final_formula $ subst_formula pre x (TVar x'))
                            (seqsubst post [₀x; as_var x] [TVar ₀x'; TVar x'])
    | PVar y ty p => if (decide (y = x))
                     then PVar y ty p
                     else PVar y ty (subst_prog p x x')
    | PConst y ty p => if (decide (y = x))
                     then PConst y ty p
                     else PConst y ty (subst_prog p x x')
  end.

  Lemma subst_prog_preserves_rank {p x x'} :
    prog_rank p = prog_rank (subst_prog p x x').
  Proof with auto.
    induction p; simpl; try lia.
    - induction gcs... f_equal. simpl. inversion H. subst. rewrite H2. f_equal.
      specialize (IHgcs H3). inversion IHgcs...
    - destruct (decide (x0 = x)); simpl...
    - destruct (decide (x0 = x)); simpl...
  Qed.

  Lemma prog_rank_ind P :
      (∀ n,
          (∀ m, m < n →
                     ∀ p', prog_rank p' = m → P p') →
          (∀ p, prog_rank p = n → P p)) →
      ∀ p, P p.
  Proof with auto.
    intros Hind.
    assert (H : ∀ n p, prog_rank p < n → P p).
    { induction n; intros p Hrank; [lia|]. apply Hind with (prog_rank p)...
      intros. apply IHn. lia. }
    intros p. apply H with (S (prog_rank p)). lia.
  Qed.

  Fixpoint prog_strong_ind (P : prog → Prop) :
    (∀ xs ts H, P (@PAsgn xs ts H)) →
    (∀ p1 p2, P p1 → P p2 → P (PSeq p1 p2)) →
    (∀ gcs, Forall (λ fp, P fp.2) gcs → P (PIf gcs)) →
    (∀ g inv v p, P p → P (PWhile g inv v p)) →
    (∀ w pre post, P (PSpec w pre post)) →
    (∀ x ty p, (∀ p', prog_rank p' = prog_rank p → P p') → P (PVar x ty p)) →
    (∀ x ty p, (∀ p', prog_rank p' = prog_rank p → P p') → P (PConst x ty p)) →
    ∀ p, P p.
  Proof with auto.
    intros Hasgn Hseq Hif Hwhile Hspec Hvar Hcons. induction p using prog_rank_ind.
    destruct p.
    - apply Hasgn.
    - apply Hseq.
      + eapply H; [|reflexivity]. subst. simpl. lia.
      + eapply H; [|reflexivity]. subst. simpl. lia.
    - apply Hif. generalize dependent n. induction gcs... intros. constructor.
      + subst. apply H with (m:=prog_rank a.2)... simpl. lia.
      + eapply IHgcs; [|reflexivity]. intros. eapply H; [|reflexivity]. subst. simpl.
        simpl in H1. lia.
    - apply Hwhile. eapply H; [|reflexivity]. subst. simpl. lia.
    - apply Hspec.
    - apply Hvar. intros. eapply H; [|reflexivity]. subst. simpl. rewrite H1. lia.
    - apply Hcons. intros. eapply H; [|reflexivity]. subst. simpl. rewrite H1. lia.
  Qed.

  Lemma PAsgn_eq {xs xs' ts ts' H H'} :
    xs = xs' →
    ts = ts' →
    @PAsgn xs ts H = @PAsgn xs' ts' H'.
  Proof. intros. subst. f_equal. apply OfSameLength_pi. Qed.

  Lemma subst_prog_non_free {p x x'} :
    as_var x ∉ prog_fvars p →
    subst_prog p x x' = p.
  Proof with auto.
    induction p; intros; simpl.
    - apply PAsgn_eq.
      + simpl in H0. apply not_elem_of_union in H0 as [? _]. clear ts H.
        induction xs; simpl... simpl in H0. destruct (decide (a = x)); [subst; set_solver|].
        f_equal. apply IHxs. set_solver.
      + simpl in H0. apply not_elem_of_union in H0 as [_ ?]. clear xs H.
        induction ts as [|t ts]... simpl in H0. simpl. f_equal.
        * apply as_final_term_eq. apply subst_term_non_free. set_solver.
        * apply IHts. set_solver.
    - f_equal; set_solver.
    - f_equal. induction gcs... simpl. f_equal.
      + destruct a. f_equal.
        * simpl. apply as_final_formula_eq. apply subst_non_free. set_solver.
        * simpl. inversion H. subst. simpl in H3. apply H3. set_solver.
      + inversion H. subst. apply IHgcs; set_solver.
    - f_equal.
      1-2: apply as_final_formula_eq; apply subst_non_free; set_solver.
      + apply as_final_term_eq. apply subst_term_non_free. set_solver.
      + apply IHp. set_solver.
    - f_equiv.
      + induction w as [|y xs]... simpl. destruct (decide (y = x)); [subst; set_solver|].
        f_equal. apply IHxs. simpl in H. simpl.
        contradict H.
        repeat rewrite elem_of_union in H. rewrite elem_of_difference in H.
        repeat rewrite elem_of_union. rewrite elem_of_difference.
        destruct_or! H.
        1-3: set_solver.
        right. assumption.
      + apply as_final_formula_eq. apply subst_non_free. set_solver.
      + simpl in H. repeat rewrite not_elem_of_union in H. destruct_and! H.
        rewrite subst_non_free.
        * rewrite subst_non_free... set_solver.
        * set_solver.
    - destruct (decide (x0 = x))... f_equal. apply IHp. set_solver.
    - destruct (decide (x0 = x))... f_equal. apply IHp. set_solver.
  Qed.

  (* ******************************************************************* *)
  (* open assignment                                                     *)
  (* ******************************************************************* *)
  Variant asgn_rhs_term :=
    | OpenRhsTerm
    | FinalRhsTerm (t : final_term).

  Record asgn_args := mkAsgnArgs {
    asgn_opens : list final_variable;
    asgn_xs : list final_variable;
    asgn_ts : list final_term;
    asgn_of_same_length : OfSameLength asgn_xs asgn_ts;
  }.

  Definition asgn_args_with_open (args : asgn_args) x :=
    let (opens, xs, ts, _) := args in
    mkAsgnArgs (x :: opens) xs ts _.

  Definition asgn_args_with_closed (args : asgn_args) x t :=
    let (opens, xs, ts, _) := args in
    mkAsgnArgs opens (x :: xs) (t :: ts) _.

  Definition split_asgn_list (xs : list final_variable) (rhs : list asgn_rhs_term)
    `{H : !OfSameLength xs rhs} : asgn_args :=
    of_same_length_rect
      id
        (λ rec x t args,
          match t with
          | OpenRhsTerm => asgn_args_with_open (rec args) x
          | FinalRhsTerm t => asgn_args_with_closed (rec args) x t
          end)
        (mkAsgnArgs [] [] [] _)
        xs rhs.

  Lemma split_asgn_list_cons_closed x t xs rhs
      `{Hl1 : !OfSameLength xs rhs} `{Hl2 : !OfSameLength (x :: xs) (FinalRhsTerm t :: rhs)} :
    @split_asgn_list (x :: xs) (FinalRhsTerm t :: rhs) Hl2  =
    asgn_args_with_closed (@split_asgn_list xs rhs Hl1) x t.
  Proof.
    unfold split_asgn_list. simpl. repeat f_equiv. apply OfSameLength_pi.
  Qed.

  Lemma split_asgn_list_cons_open x xs rhs `{!OfSameLength xs rhs}
    `{Hl' : !OfSameLength (x :: xs) (OpenRhsTerm :: rhs)} :
    @split_asgn_list (x :: xs) (OpenRhsTerm :: rhs) Hl' =
    asgn_args_with_open (split_asgn_list xs rhs) x.
  Proof.
    unfold split_asgn_list. simpl. repeat f_equiv. apply OfSameLength_pi.
  Qed.

  Lemma split_asgn_list_no_opens xs ts `{!OfSameLength xs ts} :
    split_asgn_list xs (FinalRhsTerm <$> ts) = mkAsgnArgs [] xs ts _.
  Proof with auto.
    induction_same_length xs ts as x t.
    - unfold split_asgn_list. simpl. f_equiv. apply OfSameLength_pi.
    - assert (Hl:=H'). apply of_same_length_rest in Hl.
      pose proof (@split_asgn_list_cons_closed x t xs (FinalRhsTerm <$> ts)
                    (of_same_length_fmap_r) _).
      rewrite (IH Hl) in H. unfold asgn_args_with_closed in H.
      assert (H'=of_same_length_cons) by apply OfSameLength_pi.
      rewrite H0. rewrite <- H. f_equiv. apply OfSameLength_pi.
  Qed.

  Definition PAsgnWithOpens (xs : list final_variable) (rhs : list asgn_rhs_term)
                            `{!OfSameLength xs rhs} : prog :=
    let (opens, xs, ts, _) := split_asgn_list xs rhs in
    PSeq (choose_w opens) (PAsgn xs ts).

  Lemma asgn_opens_with_open x xs rhs `{!OfSameLength xs rhs} :
    asgn_opens (asgn_args_with_open (split_asgn_list xs rhs) x) =
      x :: asgn_opens (split_asgn_list xs rhs).
  Proof.
    destruct (split_asgn_list xs rhs). simpl. reflexivity.
  Qed.

  Lemma asgn_opens_with_closed x t xs rhs `{!OfSameLength xs rhs} :
    asgn_opens (asgn_args_with_closed (split_asgn_list xs rhs) x t) =
      asgn_opens (split_asgn_list xs rhs).
  Proof.
    destruct (split_asgn_list xs rhs). simpl. reflexivity.
  Qed.

  Lemma asgn_xs_with_open x xs rhs `{!OfSameLength xs rhs} :
    asgn_xs (asgn_args_with_open (split_asgn_list xs rhs) x) =
      asgn_xs (split_asgn_list xs rhs).
  Proof.
    destruct (split_asgn_list xs rhs). simpl. reflexivity.
  Qed.

  Lemma asgn_xs_with_closed x t xs rhs `{!OfSameLength xs rhs} :
    asgn_xs (asgn_args_with_closed (split_asgn_list xs rhs) x t) =
      x :: asgn_xs (split_asgn_list xs rhs).
  Proof.
    destruct (split_asgn_list xs rhs). simpl. reflexivity.
  Qed.

  Lemma asgn_ts_with_open x xs rhs `{!OfSameLength xs rhs} :
    asgn_ts (asgn_args_with_open (split_asgn_list xs rhs) x) =
      asgn_ts (split_asgn_list xs rhs).
  Proof.
    destruct (split_asgn_list xs rhs). simpl. reflexivity.
  Qed.

  Lemma asgn_ts_with_closed x t xs rhs `{!OfSameLength xs rhs} :
    asgn_ts (asgn_args_with_closed (split_asgn_list xs rhs) x t) =
      t :: asgn_ts (split_asgn_list xs rhs).
  Proof.
    destruct (split_asgn_list xs rhs). simpl. reflexivity.
  Qed.

  Lemma asgn_opens_submseteq xs rhs `{!OfSameLength xs rhs} :
    asgn_opens (split_asgn_list xs rhs) ⊆+ xs.
  Proof with auto.
    induction_same_length xs rhs as l r; [set_solver|]. apply submseteq_cons_r.
    assert (Hl:=of_same_length_rest H'). destruct r.
    - right. erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
      eexists. split; [reflexivity | apply IH].
    - left. erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
      apply IH.
  Qed.

  Lemma asgn_xs_submseteq xs rhs `{!OfSameLength xs rhs} :
    asgn_xs (split_asgn_list xs rhs) ⊆+ xs.
  Proof with auto.
    induction_same_length xs rhs as l r; [set_solver|]. apply submseteq_cons_r.
    assert (Hl:=of_same_length_rest H'). destruct r.
    - left. erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open. apply IH.
    - right. erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed. eexists.
      split; [reflexivity | apply IH].
  Qed.

  Lemma asgn_opens_app xs1 rhs1 xs2 rhs2
    `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2}
    `{!OfSameLength (xs1 ++ xs2) (rhs1 ++ rhs2)} :
    asgn_opens (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) =
      asgn_opens (split_asgn_list xs1 rhs1) ++ asgn_opens (split_asgn_list xs2 rhs2).
  Proof with auto.
    generalize dependent rhs2. generalize dependent xs2.
    induction_same_length xs1 rhs1 as l1 r1; simpl.
    - repeat f_equiv. apply OfSameLength_pi.
    - intros. assert (Hl1:=of_same_length_rest H'). destruct r1.
      + erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
        erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
        erewrite IH. set_solver.
      + erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
        erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
        erewrite IH...
  Qed.

  Lemma asgn_xs_app xs1 rhs1 xs2 rhs2
    `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2}
    `{!OfSameLength (xs1 ++ xs2) (rhs1 ++ rhs2)} :
    asgn_xs (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) =
      asgn_xs (split_asgn_list xs1 rhs1) ++ asgn_xs (split_asgn_list xs2 rhs2).
  Proof with auto.
    generalize dependent rhs2. generalize dependent xs2.
    induction_same_length xs1 rhs1 as l1 r1; simpl.
    - repeat f_equiv. apply OfSameLength_pi.
    - intros. assert (Hl1:=of_same_length_rest H'). destruct r1.
      + erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open.
        erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open.
        erewrite IH. set_solver.
      + erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed.
        erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed.
        erewrite IH...
  Qed.

  Lemma asgn_ts_app xs1 rhs1 xs2 rhs2
    `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2}
    `{!OfSameLength (xs1 ++ xs2) (rhs1 ++ rhs2)} :
    asgn_ts (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) =
      asgn_ts (split_asgn_list xs1 rhs1) ++ asgn_ts (split_asgn_list xs2 rhs2).
  Proof with auto.
    generalize dependent rhs2. generalize dependent xs2. induction_same_length xs1 rhs1 as l1 r1;
      simpl.
    - repeat f_equiv. apply OfSameLength_pi.
    - intros. assert (Hl1:=of_same_length_rest H'). destruct r1.
      + erewrite split_asgn_list_cons_open. rewrite asgn_ts_with_open.
        erewrite split_asgn_list_cons_open. rewrite asgn_ts_with_open.
        erewrite IH. set_solver.
      + erewrite split_asgn_list_cons_closed. rewrite asgn_ts_with_closed.
        erewrite split_asgn_list_cons_closed. rewrite asgn_ts_with_closed.
        erewrite IH...
  Qed.

  Lemma elem_of_asgn_opens x xs rhs `{!OfSameLength xs rhs} :
    NoDup xs →
    x ∈ asgn_opens (split_asgn_list xs rhs) ↔ (x, OpenRhsTerm) ∈ (xs, rhs).
  Proof with auto.
    induction_same_length xs rhs as l r.
    - simpl. unfold zpair_elem_of. pose proof (elem_of_zpair_nil x (OpenRhsTerm)).
      set_solver.
    - intros. assert (Hl := of_same_length_rest H'). apply NoDup_cons in H as [].
      destruct (decide (x = l)).
      2:{ rewrite elem_of_zpair_cons_r_iff... destruct r.
          - erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
            rewrite elem_of_cons. rewrite IH... naive_solver.
          - erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
            rewrite IH... }
      subst l. destruct r.
      + erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
        rewrite elem_of_cons. rewrite IH... rewrite elem_of_zpair_cons_l_iff... split...
      + erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
        rewrite IH... rewrite elem_of_zpair_cons_l_iff... split; [|discriminate]. intros (i&?&?).
        simpl in H1, H2. apply elem_of_list_lookup_2 in H1. contradiction.
  Qed.

  Lemma elem_of_asgn_xs_ts x t xs rhs `{!OfSameLength xs rhs} :
    NoDup xs →
    (x, t) ∈ (asgn_xs (split_asgn_list xs rhs), asgn_ts (split_asgn_list xs rhs)) ↔
      (x, FinalRhsTerm t) ∈ (xs, rhs).
  Proof with auto.
    induction_same_length xs rhs as l r.
    - simpl. unfold zpair_elem_of. pose proof (elem_of_zpair_nil x t).
      pose proof (elem_of_zpair_nil x (FinalRhsTerm t)). set_solver.
    - intros. assert (Hl := of_same_length_rest H'). apply NoDup_cons in H as [].
      destruct (decide (x = l)).
      2:{ rewrite elem_of_zpair_cons_r_iff... destruct r.
          - erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open.
            rewrite asgn_ts_with_open. rewrite IH...
          - erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed.
            rewrite asgn_ts_with_closed. rewrite elem_of_zpair_cons_r_iff... }
      subst l. destruct r.
      + erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open. rewrite asgn_ts_with_open.
        rewrite IH... rewrite elem_of_zpair_cons_l_iff... split; [|discriminate]. intros (i&?&?).
        simpl in H1, H2. apply elem_of_list_lookup_2 in H1. contradiction.
      + erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed.
        rewrite asgn_ts_with_closed. rewrite (elem_of_zpair_cons_l_iff (FinalRhsTerm t))...
        split.
        * intros (i&?). destruct i.
          -- apply elem_of_zpair_indexed_cons_l in H1 as [_ ?]. subst...
          -- apply elem_of_zpair_indexed_cons_r in H1. apply elem_of_zpair_indexed_inv in H1.
             rewrite IH in H1... destruct H1 as (j&?&?). simpl in H1.
             apply elem_of_list_lookup_2 in H1. contradiction.
        * intros. inversion H1. subst t0. exists 0. split; simpl...
  Qed.

  Lemma elem_of_asgn_ts_inv t xs rhs `{!OfSameLength xs rhs} :
    t ∈ asgn_ts (split_asgn_list xs rhs) →
    ∃ x, (x, t) ∈ (asgn_xs (split_asgn_list xs rhs), (asgn_ts (split_asgn_list xs rhs))).
  Proof with auto.
    intros. apply elem_of_list_lookup in H as (i&?).
    opose proof (lookup_of_same_length_r (asgn_xs (split_asgn_list xs rhs)) H) as (x&?).
    { apply asgn_of_same_length. }
    exists x, i. split...
  Qed.

  Lemma elem_of_asgn_ts t xs rhs `{!OfSameLength xs rhs} :
    NoDup xs →
    t ∈ asgn_ts (split_asgn_list xs rhs) ↔
      ∃ x, (x, t) ∈ (asgn_xs (split_asgn_list xs rhs), (asgn_ts (split_asgn_list xs rhs))).
  Proof with auto.
    intros Hnodup. split; [apply elem_of_asgn_ts_inv|].
    intros (x&?). apply elem_of_asgn_xs_ts in H as [i []]... simpl in H, H0.
    generalize dependent i. induction_same_length xs rhs as l r; [set_solver|].
    intros Hnodup ???. assert (Hl:=of_same_length_rest H'). apply NoDup_cons in Hnodup as [].
    destruct r.
    + erewrite split_asgn_list_cons_open. rewrite asgn_ts_with_open.
      destruct i.
      * simpl in H0. discriminate.
      * apply IH with (i:=i)...
    + erewrite split_asgn_list_cons_closed. rewrite asgn_ts_with_closed. destruct i.
      * simpl in H0. inversion H0. subst. set_solver.
      * set_unfold. right. eapply IH; [assumption | exact H | exact H0].
  Qed.

  Lemma asgn_opens_Permutation xs rhs xs' rhs'
    `{!OfSameLength xs rhs} `{!OfSameLength xs' rhs'} :
    NoDup xs →
    NoDup xs' →
    (xs, rhs) ≡ₚₚ (xs', rhs') →
    asgn_opens (split_asgn_list xs rhs) ≡ₚ asgn_opens (split_asgn_list xs' rhs').
  Proof with auto.
    generalize dependent xs'. generalize dependent rhs'. induction_same_length xs rhs as l r.
    - apply zpair_Permutation_nil_inv_l in H2... destruct H2 as [-> ->]. simpl...
    - intros. apply NoDup_cons in H as []. assert (Hl:=of_same_length_rest H').
      apply zpair_Permutation_cons_inv_l in H1...
      destruct H1 as (xs'0&ys'0&xs'1&ys'1&?&?&?&?&?). destruct r.
      + erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
        subst. erewrite asgn_opens_app. erewrite split_asgn_list_cons_open.
        rewrite asgn_opens_with_open. rewrite app_Permutation_comm.
        simpl. f_equiv. etrans.
        * apply IH with (xs':=xs'0 ++ xs'1) (rhs':=ys'0 ++ ys'1)...
          apply NoDup_app in H0 as (?&?&?). apply NoDup_cons in H3 as []. apply NoDup_app.
          split_and!... intros. apply H1 in H6. set_solver.
        * erewrite asgn_opens_app. apply Permutation_app_comm.
      + erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
        subst. erewrite asgn_opens_app. erewrite split_asgn_list_cons_closed.
        rewrite asgn_opens_with_closed. rewrite app_Permutation_comm.
        simpl. etrans.
        * apply IH with (xs':=xs'0 ++ xs'1) (rhs':=ys'0 ++ ys'1)...
          apply NoDup_app in H0 as (?&?&?). apply NoDup_cons in H3 as []. apply NoDup_app.
          split_and!... intros. apply H1 in H6. set_solver.
        * erewrite asgn_opens_app. apply Permutation_app_comm.
  Qed.

  Lemma asgn_xs_ts_Permutation xs rhs xs' rhs'
    `{!OfSameLength xs rhs} `{!OfSameLength xs' rhs'} :
    NoDup xs →
    NoDup xs' →
    (xs, rhs) ≡ₚₚ (xs', rhs') →
    (asgn_xs (split_asgn_list xs rhs), asgn_ts (split_asgn_list xs rhs)) ≡ₚₚ
      (asgn_xs (split_asgn_list xs' rhs'), asgn_ts (split_asgn_list xs' rhs')).
  Proof with auto.
    generalize dependent xs'. generalize dependent rhs'. induction_same_length xs rhs as l r.
    - apply zpair_Permutation_nil_inv_l in H2... destruct H2 as [-> ->]. simpl...
    - intros. apply NoDup_cons in H as []. assert (Hl:=of_same_length_rest H').
      apply zpair_Permutation_cons_inv_l in H1...
      destruct H1 as (xs'0&ys'0&xs'1&ys'1&?&?&?&?&?). destruct r.
      + erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open. rewrite asgn_ts_with_open.
        subst.
        rewrite IH with (xs':=xs'0 ++ xs'1) (rhs':=ys'0 ++ ys'1)...
        2:{ apply NoDup_app in H0 as [? []]. apply NoDup_cons in H3 as []. apply NoDup_app.
            split_and!... intros. apply H1 in H6. set_solver. }
        repeat erewrite asgn_xs_app. repeat erewrite asgn_ts_app.
        erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open. rewrite asgn_ts_with_open...
        Unshelve. typeclasses eauto.
      + subst. erewrite asgn_xs_app. erewrite asgn_ts_app.
        repeat erewrite split_asgn_list_cons_closed. repeat erewrite asgn_xs_with_closed.
        repeat erewrite asgn_ts_with_closed. rewrite zpair_Permutation_app_comm.
        2:{ apply asgn_of_same_length. }
        2:{ eapply of_same_length_cons. Unshelve. apply asgn_of_same_length. }
        simpl. apply zpair_Permutation_cons.
        1:{ apply asgn_of_same_length. }
        1:{ eapply of_same_length_app. Unshelve. all: apply asgn_of_same_length. }
        rewrite IH with (xs':=xs'1 ++ xs'0) (rhs':=ys'1 ++ ys'0)...
        2:{ apply NoDup_app in H0 as (?&?&?). apply NoDup_cons in H3 as []. apply NoDup_app.
            split_and!... intros. intros contra. apply H1 in contra. set_solver. }
        2:{ rewrite zpair_Permutation_app_comm... }
        erewrite asgn_xs_app. erewrite asgn_ts_app...
        Unshelve. typeclasses eauto.
  Qed.

End syntax.

Arguments prog M : clear implicits.

Notation "'Δ' p" := (modified_vars p) (at level 50).

Declare Custom Entry asgn_rhs_seq.
Declare Custom Entry asgn_rhs_elem.

Notation "xs" := (xs) (in custom asgn_rhs_seq at level 0,
                       xs custom asgn_rhs_elem)
    : refiney_scope.
Notation "∅" := ([]) (in custom asgn_rhs_seq at level 0)
    : refiney_scope.

Notation "x" := ([FinalRhsTerm (as_final_term x)]) (in custom asgn_rhs_elem at level 0,
                      x custom term at level 200)
    : refiney_scope.
Notation "?" := ([OpenRhsTerm]) (in custom asgn_rhs_elem at level 0) : refiney_scope.
Notation "* x" := x (in custom asgn_rhs_elem at level 0, x constr at level 0)
    : refiney_scope.
Notation "*$( x )" := x (in custom asgn_rhs_elem at level 5, only parsing, x constr at level 200)
    : refiney_scope.
Notation "⇑ₓ xs" := (TVar ∘ as_var <$> xs)
                      (in custom asgn_rhs_elem at level 5, xs constr at level 0)
    : refiney_scope.
Notation "⇑ₓ( xs )" := (TVar ∘ as_var <$> xs)
                      (in custom asgn_rhs_elem at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑ₓ₊ xs" := (TVar <$> xs)
                      (in custom asgn_rhs_elem at level 5, xs constr at level 0)
    : refiney_scope.
Notation "⇑ₓ₊( xs )" := (TVar <$> xs)
                      (in custom asgn_rhs_elem at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑₀ xs" := (TVar ∘ initial_var_of <$> xs)
                      (in custom asgn_rhs_elem at level 5, xs constr at level 0)
    : refiney_scope.
Notation "⇑₀( xs )" := (TVar ∘ initial_var_of <$> xs)
                      (in custom asgn_rhs_elem at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑ₜ ts" := (as_term <$> ts)
                      (in custom asgn_rhs_elem at level 5, ts constr at level 0)
    : refiney_scope.
Infix "," := app (in custom asgn_rhs_elem at level 10, right associativity) : refiney_scope.

Declare Custom Entry prog.
Declare Custom Entry gcmd.

Notation "<{ e }>" := e (e custom prog) : refiney_scope.

Notation "$ e" := e (in custom prog at level 0, e constr at level 0)
    : refiney_scope.

Notation "$( e )" := e (in custom prog at level 0, only parsing,
                           e constr at level 200)
    : refiney_scope.

Notation "xs := ts" := (PAsgnWithOpens xs ts)
                       (in custom prog at level 95,
                           xs custom var_seq at level 94,
                           ts custom asgn_rhs_seq at level 94,
                           no associativity)
    : refiney_scope.

Notation "p ; q" := (PSeq p q)
                      (in custom prog at level 120, right associativity)
    : refiney_scope.

Notation "A → p" := ((as_final_formula A), p) (in custom gcmd at level 60,
                           A custom formula,
                           p custom prog,
                           no associativity) : refiney_scope.

Notation "'if' x | .. | y 'fi'" :=
  (PIf (cons (x) .. (cons (y) nil) ..))
    (in custom prog at level 95,
        x custom gcmd,
        y custom gcmd, no associativity) : refiney_scope.

Notation "'if' | g : gs → p 'fi'" := (PIf (gcmd_comprehension gs (λ g, p)))
                                     (in custom prog at level 95, g name,
                                         gs global, p custom prog)
    : refiney_scope.

Notation "'while' A 'invariant' I 'variant' v ⟶ p 'end'" :=
  (PWhile (as_final_formula A) (<!! I ∧ ⌜v ∈ₜ ℕ⌝ !!>) v p)
    (in custom prog at level 95,
        A custom formula,
        I custom formula,
        v constr at level 0,
        p custom prog, no associativity) : refiney_scope.

Notation "w : [ p , q ]" :=
  (PSpec w (as_final_formula p) q)
    (in custom prog at level 95, no associativity,
        w custom var_seq at level 94,
        p custom formula at level 85, q custom formula at level 85)
    : refiney_scope.

Notation "w : [ q ]" :=
  (PSpec w (as_final_formula <! true !>) q)
    (in custom prog at level 95, no associativity,
        w custom var_seq at level 94, q custom formula at level 85)
    : refiney_scope.

Notation ": [ p , q ]" :=
  (PSpec [] (as_final_formula p) q)
    (in custom prog at level 95, no associativity,
        p custom formula at level 85, q custom formula at level 85)
    : refiney_scope.

Notation ": [ q ]" :=
  (PSpec [] (as_final_formula <! true !>) q)
    (in custom prog at level 95, no associativity, q custom formula at level 85)
    : refiney_scope.

Notation "'|[' 'var' x .. y : ty '⦁' p ']|' " :=
  (PVar x ty .. (PVar y ty p) ..)
    (in custom prog at level 95, no associativity,
        x constr at level 0, ty custom term_ty, p custom prog) : refiney_scope.

Notation "'|[' 'var*' xs '⦁' y ']|' " :=
  (PVarList xs ⊤ y)
    (in custom prog at level 95, xs custom variable_list) : refiney_scope.

Notation "'|[' 'con' x .. y : ty '⦁' p ']|' " :=
  (PConst x ty .. (PConst y ty p) ..)
    (in custom prog at level 95, no associativity,
        x constr at level 0, ty custom term_ty, p custom prog) : refiney_scope.

Notation "'|[' 'con*' xs '⦁' y ']|' " :=
  (PConstList xs ⊤ y)
    (in custom prog at level 95, xs custom variable_list) : refiney_scope.

Notation "{ A }" := (PSpec [] (as_final_formula A) <! true !>)
                        (in custom prog at level 95, no associativity,
                            A custom formula at level 200)
    : refiney_scope.

(* Axiom M : model. *)
(* Axiom p1 p2 : @prog M. *)
(* Axiom pre : @final_formula (value M). *)
(* Axiom post : @formula (value M). *)
(* Axiom x y z : final_variable. *)
(* Axiom xs ys : list final_variable. *)
(* Definition pp := <{ $p1 ; $p2 }>. *)

(* Definition pp2 := <{ ∅ : [<! pre !>, post] }>. *)
(* Definition pp3 := <{ x, y, z := y, x, ? }> : @prog M. *)
(* Definition pp4 := <{ x : [pre, post] }> : @prog M. *)

Section semantics.
  Context {M : model}.
  Context {MNat : ModelWithNat M}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation prog := (prog M).
  Local Notation term := (term M).
  Local Notation formula := (formula M).
  Local Notation final_term := (final_term M).
  Local Notation final_formula := (final_formula M).

  Local Definition while_fvars (g inv : final_formula) (var : final_term) (p : prog) :=
    formula_fvars inv ∪ formula_fvars g ∪ term_fvars var ∪ prog_fvars p.

  Fixpoint wp (p : prog) (A : formula) : formula :=
    match p with
    | PAsgn xs ts => <! A [[ ↑ₓ xs \ ⇑ₜ ts]] !>
    | PSeq p1 p2 => wp p1 (wp p2 A)
    | PIf gcs => <! ∨* ⤊(gcs.*1) ∧
                      ∧* (map (λ gc, <! $(as_formula gc.1) ⇒ $(wp gc.2 A) !>) gcs) !>
    | PWhile g inv var p =>
        let var₀ := fresh_var (raw_var "") (while_fvars g inv var p) in
        <! ∀* $(set_to_list (Δ p)),
            (inv ∧ g ⇒ $(wp p inv)) ∧
            (inv ∧ ¬ g ⇒ A) ∧
            (inv ∧ g ⇒ ⌜var ∈ₜ ℕ⌝) ∧
            (∀ var₀, inv ∧ g ∧ ⌜var = var₀⌝ ⇒ $(wp p (<! ⌜var < var₀⌝ !>))) !>
    | PSpec w pre post =>
        <! pre ∧ (∀* ↑ₓ w, post ⇒ A)[_₀\*]  !>
    | PVar x ty p =>
        let x' := fresh_var x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A) in
        <! (∀ x : ty, $(wp p <! A[x \ x'] !>))[x' \ x] !>
    | PConst x ty p =>
        let x' := fresh_var x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A) in
        <! (∃ x : ty, $(wp p <! A[x \ x'] !>))[x' \ x] !>
    end.

  Global Instance wp_final {p A} `{!FormulaFinal A} : FormulaFinal (wp p A).
  Proof with auto.
    generalize dependent A. induction p; intros; simpl; try typeclasses eauto.
    unshelve eapply f_and_formula_final. unfold FormulaFinal in *. unfold formula_final.
    intros. set_unfold in H0. destruct H0 as (B&(gc&->&?)&?). destruct gc. simpl in *.
    apply elem_of_union in H1 as [|].
    - apply (final_formula_final _ _ H1).
    - rewrite Forall_forall in H. unfold elem_of in H1. specialize (H (f, p) H0).
      simpl in H. specialize (H A FormulaFinal0). apply H...
  Qed.

  Lemma fvars_wp {p A} `{!FormulaFinal A} :
    formula_fvars (wp p A) ⊆ prog_fvars p ∪ formula_fvars A.
  Proof with auto.
    intros. generalize dependent A. induction p; intros; intros z; intros.
    - simpl in *. apply fvars_msubst_superset in H0.
      set_unfold in H0. destruct H0; [set_solver|]. set_unfold.
      left. right. apply elem_of_union_list. destruct H0 as (?&?&?&?&?).
      exists (term_fvars x). split... set_unfold. subst. exists x0. split...
    - simpl. simpl in H. apply IHp1 in H; [|typeclasses eauto]. set_solver.
    - simpl in *. induction gcs.
      + simpl. set_solver.
      + simpl. inversion H. subst. set_solver.
    - simpl in *. rewrite fvars_foralllist in H. simpl in *. set_unfold in H.
      destruct H. destruct_or! H.
      1-2: set_solver.
      2-7: set_solver.
      1:{ apply IHp in H... set_solver. }
      destruct H. destruct_or! H.
      1-4: set_solver.
      specialize (IHp <!! ⌜ v < $(fresh_var ""%string (while_fvars g inv v p)) ⌝ !!>).
      apply IHp in H... set_solver.
    - simpl in *. apply elem_of_union in H as [|]; [set_solver|].
      apply elem_of_subst_all_initials_fvars in H as [].
      destruct H0; rewrite fvars_foralllist in H0.
      + set_unfold in H0. rewrite not_and_l in H0. destruct H0. destruct H0; [|set_solver].
        destruct H1.
        * set_solver.
        * set_unfold. left. left. right. split... apply not_and_l. right.
          apply var_final_not_initial...
      + set_unfold in H0. rewrite not_and_l in H0. destruct H0. destruct H0; [set_solver|].
        apply formula_is_final in H0... apply var_final_not_initial in H0...
    - simpl wp in H. apply elem_of_subst_fvars in H. destruct H as [[] | []].
      + simpl in H. set_unfold in H. destruct H. destruct H; [contradiction|].
        apply IHp in H... set_unfold in H. destruct H; set_solver.
      + pose proof (fresh_var_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A)).
        set_unfold in H0. subst. simpl in H. set_unfold in H. destruct H.
        destruct H; [contradiction|]. apply IHp in H... set_solver.
    - simpl wp in H. apply elem_of_subst_fvars in H. destruct H as [[] | []].
      + simpl in H. set_unfold in H. destruct H. destruct H; [contradiction|].
        apply IHp in H... set_unfold in H. destruct H; set_solver.
      + pose proof (fresh_var_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A)).
        set_unfold in H0. subst. simpl in H. set_unfold in H. destruct H.
        destruct H; [contradiction|]. apply IHp in H... set_solver.
  Qed.

  Local Definition k_subst p := ∀ (x : variable) (t : term) A,
    VarFinal x →
    FormulaFinal A →
    TermFinal t →
    x ∉ prog_fvars p →
    term_fvars t ## prog_fvars p →
    <! $(wp p A)[x \ t] !> ≡ wp p <! A[x \ t] !>.

  Local Definition k_congr p := ∀ A B, FormulaFinal A → FormulaFinal B → A ≡ B → wp p A ≡ wp p B.

  Local Definition k_var p := ∀ x ty A y,
    VarFinal y →
    FormulaFinal A →
    as_var x ≠ y →
    y ∉ prog_fvars p →
    y ∉ formula_fvars A →
    wp (PVar x ty p) A ≡ <! (∀ x : ty, $(wp p <! A[x \ y] !>))[y \ x] !>.

  Local Definition k_const p := ∀ x ty A y,
    VarFinal y →
    FormulaFinal A →
    as_var x ≠ y →
    y ∉ prog_fvars p →
    y ∉ formula_fvars A →
    wp (PConst x ty p) A ≡ <! (∃ x : ty, $(wp p <! A[x \ y] !>))[y \ x] !>.

  Lemma L_var' p :
    k_congr p →
    k_subst p →
    ∀ (x : final_variable) ty A (y z : variable) `{VarFinal y} `{VarFinal z} `{!FormulaFinal A},
      as_var x ≠ y →
      y ∉ prog_fvars p →
      y ∉ formula_fvars A →
      as_var x ≠ z →
      z ∉ prog_fvars p →
      z ∉ formula_fvars A →
      <! (∀ x : ty, $(wp p <! A[x \ y] !>))[y \ x] !> ⇛
        <! (∀ x : ty, $(wp p <! A[x \ z] !>))[z \ x] !>.
  Proof with auto.
    intros Hcongr Hsubst. intros x ty A y z Hy Hz Ha Hne1 Hp1 Ha1 Hne2 Hp2 Ha2.
    destruct (decide (y = z)).
    { rewrite <- e in *. reflexivity. }
    intros σ?.
    unfold FForallT in *.
    rewrite <- f_forall_one_point by set_solver.
    rewrite <- f_forall_one_point in H by set_solver.
    rewrite fforall_alpha_equiv with (x':=y).
    2:{
      intros contra. simpl in contra. set_unfold in contra. destruct contra.
      - destruct H0; [done|]. subst. set_solver.
      - destruct H0. destruct H0; [contradiction|]. apply fvars_wp in H0. set_solver.
    }
    rewrite simpl_subst_impl. rewrite simpl_subst_af. simpl.
    destruct (decide _); [|contradiction].
    destruct (decide _); [done|].
    clear e n. revert H. revert σ. rewrite fold_fent. f_equiv. f_equiv.
    intros σ?. rewrite simpl_subst_forall.
    2:{ unfold quant_subst_fvars. set_solver. }
    rewrite simpl_subst_impl. rewrite simpl_subst_af. simpl.
    destruct (decide _); [done|].
    clear n. revert H. revert σ. rewrite fold_fent. f_equiv. f_equiv.
    intros σ?.
    eapply (Hsubst z (as_final_term y) <! A [x \ z] !> _ _ _ Hp2 _ σ).
    clear Hsubst.
    unfold k_congr in Hcongr.
    revert H. apply Hcongr... apply fequiv_subst_trans...
    Unshelve. simpl. set_solver.
  Qed.

  Lemma L_var p : k_congr p → k_subst p → k_var p.
  Proof with auto.
    intros. unfold k_var. intros. simpl.
    mk_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A) as z.
    repeat rewrite not_elem_of_union in H4. destruct_and! H6.
    apply fequiv_fent. split.
    - apply L_var'... set_solver.
    - apply L_var'... set_solver.
  Qed.

  Lemma L_const' p :
    k_congr p →
    k_subst p →
    ∀ (x : final_variable) ty A (y z : variable) `{VarFinal y} `{VarFinal z} `{!FormulaFinal A},
      as_var x ≠ y →
      y ∉ prog_fvars p →
      y ∉ formula_fvars A →
      as_var x ≠ z →
      z ∉ prog_fvars p →
      z ∉ formula_fvars A →
      <! (∃ x : ty, $(wp p <! A[x \ y] !>))[y \ x] !> ⇛
        <! (∃ x : ty, $(wp p <! A[x \ z] !>))[z \ x] !>.
  Proof with auto.
    intros Hcongr Hsubst. intros x ty A y z Hy Hz Ha Hne1 Hp1 Ha1 Hne2 Hp2 Ha2.
    destruct (decide (y = z)).
    { rewrite <- e in *. reflexivity. }
    intros σ?.
    unfold FExistsT in *.
    rewrite <- f_exists_one_point by set_solver.
    rewrite <- f_exists_one_point in H by set_solver.
    rewrite fexists_alpha_equiv with (x':=y).
    2:{
      intros contra. simpl in contra. set_unfold in contra. destruct contra.
      - destruct H0; [done|]. subst. set_solver.
      - destruct H0. destruct H0; [contradiction|]. apply fvars_wp in H0. set_solver.
    }
    rewrite simpl_subst_and. rewrite simpl_subst_af. simpl.
    destruct (decide _); [|contradiction].
    destruct (decide _); [done|].
    clear e n. revert H. revert σ. rewrite fold_fent. f_equiv. f_equiv.
    intros σ?. rewrite simpl_subst_exists.
    2:{ unfold quant_subst_fvars. set_solver. }
    rewrite simpl_subst_and. rewrite simpl_subst_af. simpl.
    destruct (decide _); [done|].
    clear n. revert H. revert σ. rewrite fold_fent. f_equiv. f_equiv.
    intros σ?.
    eapply (Hsubst z (as_final_term y) <! A [x \ z] !> _ _ _ Hp2 _ σ).
    clear Hsubst.
    unfold k_congr in Hcongr.
    revert H. apply Hcongr... apply fequiv_subst_trans...
    Unshelve. simpl. set_solver.
  Qed.

  Lemma L_const p : k_congr p → k_subst p → k_const p.
  Proof with auto.
    intros. unfold k_const. intros. simpl.
    mk_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A) as z.
    repeat rewrite not_elem_of_union in H4. destruct_and! H6.
    apply fequiv_fent. split.
    - apply L_const'... set_solver.
    - apply L_const'... set_solver.
  Qed.

  Local Lemma L_congr p :
    (∀ p' : prog, prog_rank p' < prog_rank p → k_var p' ∧ k_const p') →
    k_congr p.
  Proof with auto.
    unfold k_congr. induction p using prog_strong_ind; intros.
    - simpl. rewrite H3...
    - simpl. apply IHp1... 2: apply IHp2...
      + intros. apply H... simpl. lia.
      + intros. apply H... simpl. lia.
    - simpl. f_equiv. generalize dependent B. generalize dependent A.
      induction gcs; intros; simpl... apply Forall_cons in H as [].
      rewrite H with (B:=B)...
      2: {intros. apply H0... simpl. lia. }
      f_equiv. apply IHgcs... intros. apply H0... simpl. simpl in *. lia.
    - simpl. do 3 f_equiv. by rewrite H2.
    - simpl. f_equiv. f_equiv. by rewrite H2.
    - simpl. mk_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A ∪ formula_fvars B) as z.
      assert (H6:=H0). simpl in H0. forward (H0 p) by lia.
      assert (k_var p) by naive_solver. unfold k_var in H5.
      simpl in H5. rewrite H5 with (y:=z)...
      2-4: set_solver.
      rewrite H5 with (y:=z)...
      2-4: set_solver.
      do 2 f_equiv. apply H...
      + intros. apply H6... simpl. lia.
      + f_equiv...
    - simpl. mk_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A ∪ formula_fvars B) as z.
      assert (H6:=H0). simpl in H0. forward (H0 p) by lia.
      assert (k_const p) by naive_solver. unfold k_const in H5.
      simpl in H5. rewrite H5 with (y:=z)...
      2-4: set_solver.
      rewrite H5 with (y:=z)...
      2-4: set_solver.
      do 2 f_equiv. apply H...
      + intros. apply H6... simpl. lia.
      + f_equiv...
  Qed.

  Lemma PSpec_finalized_initial_fvars (w : list final_variable)  (post A : formula) `{!FormulaFinal A} :
    finalized_initial_fvars <! (∀* ↑ₓ w, post ⇒ A) !> ≡ₚ finalized_initial_fvars post.
  Proof with auto.
    unfold finalized_initial_fvars, initial_fvars.
    rewrite fvars_foralllist. f_equiv.
    rewrite filter_set_to_list_delete_difference.
    2:{ intros. apply elem_of_list_to_set in H. set_unfold. destruct H as (?&->&?).
        set_solver. }
    simpl. rewrite filter_set_to_list_delete_union_r...
    intros. apply formula_is_final in H. apply var_final_not_initial...
  Qed.

  Local Lemma L_subst p :
    (∀ p', prog_rank p' < prog_rank p → k_congr p' ∧ k_var p' ∧ k_const p') →
    k_subst p.
  Proof with auto.
    unfold k_subst. induction p using prog_strong_ind;
      intros Hind ??? Hfinal1 Hfinal2 Hfinal3; intros.
    - simpl. simpl in H0. apply not_elem_of_union in H0 as []. rewrite msubst_subst_comm...
      + contradict H0. apply elem_of_list_to_set...
      + set_unfold. contradict H2. apply elem_of_union_list. destruct H2 as (t'&?&x'&?&?).
        subst. exists (term_fvars x'). split... set_unfold. eauto.
      + set_solver.
    - simpl. rewrite IHp1...
      + apply Hind; auto; [simpl; lia|]. apply IHp2...
        * intros. apply Hind. simpl. lia.
        * set_solver.
        * set_solver.
      + intros. apply Hind. simpl. lia.
      + set_solver.
      + set_solver.
    - simpl. rewrite simpl_subst_and. simpl in H0. f_equiv.
      + rewrite subst_non_free... contradict H0.
        set_unfold in H0. simpl in H0. apply elem_of_union_list.
        destruct H0 as (?&(B&->&([]&->&?))&?). simpl in *.
        exists (prog_fvars p ∪ formula_fvars f).
        split; [|set_solver]. set_unfold. exists (f, p). simpl. set_solver.
      + induction gcs; simpl... inversion H. subst. rewrite simpl_subst_and. f_equiv.
        * rewrite simpl_subst_impl. f_equiv.
          -- rewrite subst_non_free... simpl in H1. set_solver.
          -- apply H4...
             ++ intros. apply Hind. simpl. lia.
             ++ set_solver.
             ++ set_solver.
        * apply IHgcs...
          -- intros. apply Hind. simpl. simpl in H2. lia.
          -- set_solver.
          -- set_solver.
    - simpl. rewrite simpl_subst_foralllist.
      2:{ contradict H. apply elem_of_set_to_list in H. apply modified_vars_subseteq_fvars in H.
          set_solver. }
      2:{ intros z??. rewrite list_to_set_set_to_list in H1.
          apply modified_vars_subseteq_fvars in H1. set_solver. }
      f_equiv. rewrite simpl_subst_and.
      rewrite simpl_subst_impl. rewrite simpl_subst_and.
      rewrite subst_non_free by set_solver.
      rewrite subst_non_free by set_solver.
      rewrite IHp...
      2:{ intros. apply Hind. simpl in *. lia. }
      2-3: set_solver.
      f_equiv.
      { f_equiv. apply Hind... rewrite subst_non_free... set_solver. }
      rewrite simpl_subst_and. rewrite simpl_subst_impl. rewrite simpl_subst_and.
      rewrite subst_non_free by set_solver. rewrite subst_non_free by set_solver.
      f_equiv. rewrite simpl_subst_and. rewrite simpl_subst_impl. rewrite simpl_subst_and.
      rewrite subst_non_free by set_solver. rewrite subst_non_free by set_solver.
      rewrite simpl_subst_af. simpl. rewrite subst_term_non_free by set_solver.
      f_equiv. mk_fresh (while_fvars g inv v p) as y.
      mk_fresh ({[x]} ∪
          prog_fvars p ∪
          formula_fvars <! inv ∧ g ∧ ⌜ v = y ⌝ ⇒ $(wp p <! ⌜ v < y ⌝ !>) !> ∪
            quant_subst_fvars y <! inv ∧ g ∧ ⌜ v = y ⌝ ⇒ $(wp p <! ⌜ v < y ⌝ !>) !> x t)
        as z.
      rewrite fforall_alpha_equiv with (x':=z) by set_solver.
      rewrite simpl_subst_forall by set_solver. f_equiv.
      repeat rewrite simpl_subst_impl. repeat rewrite simpl_subst_and.
      rewrite subst_non_free with (x:=y) by set_solver.
      rewrite subst_non_free with (x:=x) by set_solver.
      rewrite subst_non_free with (x:=y) by set_solver.
      rewrite subst_non_free with (x:=x) by set_solver.
      repeat rewrite simpl_subst_af. simpl. destruct (decide _); [|contradiction]. clear e.
      rewrite subst_term_non_free with (x:=y) by set_solver.
      rewrite subst_term_non_free with (x:=x) by set_solver.
      repeat rewrite simpl_subst_af. simpl. destruct (decide _); [set_solver|]. clear n.
      f_equiv. erewrite IHp...
      2:{ intros. apply Hind. simpl in *. lia. }
      3-4: set_solver.
      2: typeclasses eauto.
      rewrite IHp...
      2:{ intros. apply Hind. simpl in *. lia. }
      2-3: set_solver.
      apply Hind... unfold term_lt. repeat rewrite simpl_subst_af.
      simpl. destruct (decide _); [|contradiction]. clear e. simpl.
      destruct (decide _); [set_solver|]. rewrite subst_term_non_free with (t:=v) by set_solver.
      rewrite subst_term_non_free with (t:=v) by set_solver...
    - simpl. rewrite simpl_subst_and. rewrite subst_non_free by set_solver.
      f_equiv. simpl in H. repeat rewrite not_elem_of_union in H. destruct_and! H.
      apply not_elem_of_difference in H3. apply not_elem_of_list_to_set in H1.
      unfold subst_all_initials. do 2 rewrite subst_initials_msubst.
      rewrite msubst_subst_comm.
      2:{ intros contra. set_unfold in contra. destruct contra as (?&->&?&?).
          apply not_and_l in H5. destruct H5; [set_solver|].
          destruct H; [set_solver|]. apply formula_is_final in H... }
      2:{ intros contra. set_unfold in contra. destruct contra as (?&?&?).
          rewrite not_and_l in H6. destruct H6; [set_solver|]. destruct H5; [set_solver|].
          apply formula_is_final in H5... }
      2: set_solver.
      do 2 rewrite <- subst_initials_msubst. f_equiv.
      2:{ rewrite PSpec_finalized_initial_fvars... rewrite PSpec_finalized_initial_fvars... }
      rewrite simpl_subst_foralllist...
      2: set_solver.
      rewrite simpl_subst_impl.
      rewrite subst_non_free...
      destruct H3... set_unfold in H. destruct H. apply var_initial_not_final in H3.
      destruct (H3 var_is_final).
    - assert (k_var p) by (apply Hind; naive_solver). unfold k_var in H2.
      mk_fresh ({[as_var x]} ∪
          {[x0]} ∪
          prog_fvars p ∪
          formula_fvars A ∪
          term_fvars t)
        as y.
      rewrite H2 with (y:=y) by set_solver.
      rewrite H2 with (y:=y) by set_solver.
      unfold FForallT.
      mk_fresh (formula_fvars <! ⌜ x ∈ₜ ty ⌝ ⇒ $(wp p <! A [x \ y] !>) !> ∪
          formula_fvars <! ⌜ x ∈ₜ ty ⌝ ⇒ $(wp p <! A [x0 \ t] [x \ y] !>) !> ∪
          {[as_var x]} ∪
          {[y]} ∪
          {[x0]} ∪
          prog_fvars p ∪
          formula_fvars A ∪
          term_fvars t)
        as z.
      rewrite fforall_alpha_equiv with (x':=z) by set_solver.
      rewrite fforall_alpha_equiv with (x:=x) (x':=z) by set_solver.
      rewrite simpl_subst_forall by set_solver.
      rewrite simpl_subst_forall by set_solver.
      rewrite simpl_subst_forall by set_solver.
      f_equiv. repeat rewrite simpl_subst_impl. repeat rewrite simpl_subst_af.
      simpl. destruct (decide _); [|contradiction]. clear e.
      rewrite subst_term_non_free with (x:=y) by set_solver.
      rewrite subst_term_non_free with (x:=x0) by set_solver.
      f_equiv.
      destruct (decide (as_var x = x0)).
      {
        subst. rewrite fequiv_subst_trans by set_solver.
        mk_fresh
          ({[as_var x; y; z]} ∪ formula_fvars (wp p <! A [x \ y] !>) ∪ term_fvars t
             ∪ prog_fvars p ∪ formula_fvars (wp p <! A [x \ t] [x \ y] !>))
          as w.
        rewrite subst_subst_ne' with (z:=w) by set_solver.
        rewrite subst_subst_ne' with (x2:=y) (z:=w) by set_solver.
        rewrite H...
        2:{ intros. apply Hind. simpl in *. lia. }
        2: typeclasses eauto.
        2: set_solver.
        2:{ intros i??. apply fvars_subst_term_superset in H6. set_solver. }
        rewrite H with (x:=y)...
        2:{ intros. apply Hind. simpl in *. lia. }
        2: typeclasses eauto.
        2: set_solver.
        2:{ intros i??. apply fvars_subst_term_superset in H6. set_solver. }
        do 2 f_equiv. apply Hind...
        rewrite fequiv_subst_trans by set_solver.
        rewrite fequiv_subst_trans by set_solver.
        simpl. destruct (decide (as_var x = as_var x)); [|contradiction].
        rewrite subst_subst_eq...
      }
      symmetry.
      trans (<! $(wp p <! A [x \ y] !>) [x0 \ t [x \ y]] [x \ z] [y \ x] !>).
      { do 2 f_equiv.
        rewrite H...
        2: { intros. apply Hind. simpl in *. lia. }
        2: typeclasses eauto.
        2: set_solver.
        2:{ intros i??. apply fvars_subst_term_superset in H5. set_solver. }
        apply Hind... rewrite subst_subst_ne; set_solver. }
      rewrite subst_subst_ne with (x2:=x) by set_solver.
      rewrite subst_term_non_free.
      2:{ intros contra. apply fvars_subst_term_superset in contra. set_solver. }
      rewrite subst_subst_ne with (x1:=x0) (x2:=y) by set_solver.
      rewrite subst_term_trans by set_solver.
      rewrite subst_term_diag...
    - assert (k_const p) by (apply Hind; naive_solver). unfold k_const in H2.
      mk_fresh ({[as_var x]} ∪
          {[x0]} ∪
          prog_fvars p ∪
          formula_fvars A ∪
          term_fvars t)
        as y.
      rewrite H2 with (y:=y) by set_solver.
      rewrite H2 with (y:=y)...
      2-4: set_solver.
      unfold FExistsT.
      mk_fresh (formula_fvars <! ⌜ x ∈ₜ ty ⌝ ⇒ $(wp p <! A [x \ y] !>) !> ∪
          formula_fvars <! ⌜ x ∈ₜ ty ⌝ ⇒ $(wp p <! A [x0 \ t] [x \ y] !>) !> ∪
          {[as_var x]} ∪
          {[y]} ∪
          {[x0]} ∪
          prog_fvars p ∪
          formula_fvars A ∪
          term_fvars t)
        as z.
      rewrite fexists_alpha_equiv with (x':=z) by set_solver.
      rewrite fexists_alpha_equiv with (x:=x) (x':=z) by set_solver.
      rewrite simpl_subst_exists by set_solver.
      rewrite simpl_subst_exists by set_solver.
      rewrite simpl_subst_exists by set_solver.
      f_equiv. repeat rewrite simpl_subst_and. repeat rewrite simpl_subst_af.
      simpl. destruct (decide _); [|contradiction]. clear e.
      rewrite subst_term_non_free with (x:=y) by set_solver.
      rewrite subst_term_non_free with (x:=x0) by set_solver.
      f_equiv.
      destruct (decide (as_var x = x0)).
      {
        subst. rewrite fequiv_subst_trans by set_solver.
        mk_fresh
          ({[as_var x; y; z]} ∪ formula_fvars (wp p <! A [x \ y] !>) ∪ term_fvars t
             ∪ prog_fvars p ∪ formula_fvars (wp p <! A [x \ t] [x \ y] !>))
          as w.
        rewrite subst_subst_ne' with (z:=w) by set_solver.
        rewrite subst_subst_ne' with (x2:=y) (z:=w) by set_solver.
        rewrite H...
        2:{ intros. apply Hind. simpl in *. lia. }
        2: typeclasses eauto.
        2: set_solver.
        2:{ intros i??. apply fvars_subst_term_superset in H6. set_solver. }
        rewrite H with (x:=y)...
        2:{ intros. apply Hind. simpl in *. lia. }
        2: typeclasses eauto.
        2: set_solver.
        2:{ intros i??. apply fvars_subst_term_superset in H6. set_solver. }
        do 2 f_equiv. apply Hind...
        rewrite fequiv_subst_trans by set_solver.
        rewrite fequiv_subst_trans by set_solver.
        simpl. destruct (decide (as_var x = as_var x)); [|contradiction].
        rewrite subst_subst_eq...
      }
      symmetry.
      trans (<! $(wp p <! A [x \ y] !>) [x0 \ t [x \ y]] [x \ z] [y \ x] !>).
      { do 2 f_equiv.
        rewrite H...
        2: { intros. apply Hind. simpl in *. lia. }
        2: typeclasses eauto.
        2: set_solver.
        2:{ intros i??. apply fvars_subst_term_superset in H5. set_solver. }
        apply Hind... rewrite subst_subst_ne; set_solver. }
      rewrite subst_subst_ne with (x2:=x) by set_solver.
      rewrite subst_term_non_free.
      2:{ intros contra. apply fvars_subst_term_superset in contra. set_solver. }
      rewrite subst_subst_ne with (x1:=x0) (x2:=y) by set_solver.
      rewrite subst_term_trans by set_solver. rewrite subst_term_diag...
  Qed.

  Local Lemma L p : k_congr p ∧ k_const p ∧ k_subst p ∧ k_var p.
  Proof with auto.
    induction p using prog_rank_ind.
    assert (k_congr p) by (apply L_congr; naive_solver).
    assert (k_subst p) by (apply L_subst; naive_solver).
    split_and!...
    - apply L_const...
    - apply L_var...
  Qed.

  Lemma wp_subst p A (x : variable) (t : term) `{!FormulaFinal A} `{VarFinal x} `{!TermFinal t} :
    x ∉ prog_fvars p →
    term_fvars t ## prog_fvars p →
    <! $(wp p A)[x \ t] !> ≡ wp p <! A[x \ t] !>.
  Proof. by apply L. Qed.

  Lemma wp_congr p A B `{!FormulaFinal A} `{!FormulaFinal B} :
    A ≡ B →
    wp p A ≡ wp p B.
  Proof. by apply L. Qed.

  Lemma wp_var p x ty A y `{!FormulaFinal A} `{VarFinal y} :
    as_var x ≠ y →
    y ∉ prog_fvars p →
    y ∉ formula_fvars A →
    wp (PVar x ty p) A ≡ <! (∀ x : ty, $(wp p <! A[x \ y] !>))[y \ x] !>.
  Proof. by apply L. Qed.

  Lemma wp_const p x ty A y `{!FormulaFinal A} `{VarFinal y} :
    as_var x ≠ y →
    y ∉ prog_fvars p →
    y ∉ formula_fvars A →
    wp (PConst x ty p) A ≡ <! (∃ x : ty, $(wp p <! A[x \ y] !>))[y \ x] !>.
  Proof. by apply L. Qed.

  Lemma wp_while_decrease_variant {g inv : final_formula} {var : final_term} {p} y `{VarFinal y} :
    y ∉ formula_fvars g →
    y ∉ formula_fvars inv →
    y ∉ term_fvars var →
    y ∉ prog_fvars p →
    let var₀ := fresh_var (raw_var "") (while_fvars g inv var p) in
        <! (∀ var₀, inv ∧ g ∧ ⌜var = var₀⌝ ⇒ $(wp p (<! ⌜var < var₀⌝ !>))) !> ≡
        <! (∀ y, inv ∧ g ∧ ⌜var = y⌝ ⇒ $(wp p (<! ⌜var < y⌝ !>))) !>.
  Proof with auto.
    intros.
    destruct (decide (y = var₀)).
    { subst... }
    mk_fresh (while_fvars g inv var p) as x.
    rewrite fforall_alpha_equiv with (x':=y).
    - rewrite simpl_subst_impl. repeat rewrite simpl_subst_and...
      repeat rewrite simpl_subst_af. unfold while_fvars in H3.
      rewrite subst_non_free by set_solver.
      rewrite subst_non_free by set_solver.
      simpl. destruct (decide _); [|contradiction].
      rewrite subst_term_non_free by set_solver.
      do 2 f_equiv. rewrite wp_subst...
      2: typeclasses eauto.
      2-3: set_solver.
      f_equiv.
      unfold term_lt.
      rewrite simpl_subst_af.
      simpl. destruct (decide _); [|contradiction].
      rewrite subst_term_non_free... set_solver.
    - clear H4. intros contra. simpl in contra. set_unfold in contra.
      destruct_or! contra.
      1-4: set_solver.
      apply fvars_wp in contra. simpl in contra. set_solver.
  Qed.

  Lemma wp_congr_fent p A B `{!FormulaFinal A} `{!FormulaFinal B} :
    A ⇛ B →
    wp p A ⇛ wp p B.
  Proof with auto.
    generalize dependent B. generalize dependent A. induction p; intros; simpl...
    - by rewrite H0.
    - f_equiv. induction gcs.
      + simpl...
      + simpl. inversion H. subst. f_equiv... f_equiv...
    - do 3 f_equiv. rewrite H...
    - f_equiv. unfold subst_all_initials. rewrite PSpec_finalized_initial_fvars...
      rewrite PSpec_finalized_initial_fvars... rewrite H...
    - mk_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A ∪ formula_fvars B) as y.
      pose proof (wp_var). simpl in H1.
      rewrite H1 with (y:=y)...
      2-4: set_solver.
      rewrite H1 with (y:=y)...
      2-4: set_solver.
      do 2 f_equiv.
      apply IHp... rewrite H...
    - mk_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A ∪ formula_fvars B) as y.
      pose proof (wp_const). simpl in H1.
      rewrite H1 with (y:=y)...
      2-4: set_solver.
      rewrite H1 with (y:=y)...
      2-4: set_solver.
      do 2 f_equiv.
      apply IHp... rewrite H...
  Qed.

  (* ******************************************************************* *)
  (* definition and properties of ⊑ and ≡ on prog                        *)
  (* ******************************************************************* *)
  Global Instance refines : SqSubsetEq prog := λ p1 p2,
    ∀ A : final_formula, wp p1 A ⇛ (wp p2 A).

  Global Instance pequiv : Equiv prog := λ p1 p2, ∀ A : final_formula, wp p1 A ≡ wp p2 A.
  Global Instance refines_refl : Reflexive refines.
  Proof with auto. intros ??. reflexivity. Qed.

  Global Instance refines_trans : Transitive refines.
  Proof with auto. intros p1 p2 p3 ?? A... transitivity (wp p2 A); naive_solver. Qed.

  Global Instance pequiv_refl : Reflexive pequiv.
  Proof with auto. split; done. Qed.

  Global Instance pequiv_sym : Symmetric pequiv.
  Proof with auto. intros p1 p2. unfold pequiv. intros. symmetry... Qed.

  Global Instance pequiv_trans : Transitive pequiv.
  Proof with auto. intros p1 p2 p3 ?? A. trans (wp p2 A)... Qed.

  Global Instance pequiv_equiv : Equivalence pequiv.
  Proof. split; [exact pequiv_refl | exact pequiv_sym | exact pequiv_trans]. Qed.

  Global Instance refines_antisym : Antisymmetric prog pequiv refines.
  Proof with auto.
    intros p1 p2 H12 H21. split; intros; [apply H12 in H | apply H21 in H]...
  Qed.

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w : list final_variable.
  Implicit Types xs : list final_variable.
  Implicit Types t : term.

  Lemma wp_asgn xs ts A `{!OfSameLength xs ts} `{!FormulaFinal A} :
    wp <{ *xs := *$(FinalRhsTerm <$> ts) }> A ≡ <! A[[ ↑ₓ xs \ ⇑ₜ ts]] !>.
  Proof with auto.
    unfold PAsgnWithOpens. rewrite split_asgn_list_no_opens. simpl.
    fSimpl. unfold subst_all_initials. apply f_subst_initials_no_initials.
    intros x ??. set_unfold. apply fvars_msubst_superset in H0. set_unfold.
    destruct H as [? _]. destruct H0 as [| (?&?&t&->&?)].
    - apply formula_is_final in H0...
    - apply term_is_final in H0...
  Qed.

  Global Instance wp_proper_pequiv {A : formula} `{!FormulaFinal A} :
    Proper ((≡) ==> (≡)) (λ p, wp p A).
  Proof. intros p1 p2 Hp. specialize (Hp <!! A !!>). assumption. Qed.

  Global Instance wp_proper_ref {A : formula} `{!FormulaFinal A} :
    Proper ((⊑) ==> (⇛)) (λ p, wp p A).
  Proof. intros p1 p2 Hp. specialize (Hp <!! A !!>). assumption. Qed.

  Global Instance PVar_proper : Proper ((=) ==> (=) ==> (≡) ==> (≡@{prog})) PVar.
  Proof with auto.
    intros x ? <- ty ? <- A B ? C.
    mk_fresh x ({[as_var x]} ∪ prog_fvars A ∪ prog_fvars B ∪ formula_fvars C) as y.
    rewrite wp_var with (y:=y)...
    2-4: set_solver.
    rewrite wp_var with (y:=y)...
    2-4: set_solver.
    do 2 f_equiv. apply wp_proper_pequiv...
  Qed.

  Global Instance PVarList_proper : Proper ((=) ==> (=) ==> (≡) ==> (≡@{prog})) PVarList.
  Proof with auto.
    intros xs ? <- ty ? <- A B ?. induction xs as [|x xs IH].
    - simpl. apply H.
    - intros C.
      mk_fresh x ({[as_var x]} ∪ prog_fvars (PVarList xs ty A)
                    ∪ prog_fvars (PVarList xs ty B) ∪ formula_fvars C) as y.
      simpl. pose proof wp_var. simpl in H1.
      rewrite H1 with (y:=y)...
      2-4: set_solver.
      rewrite H1 with (y:=y)...
      2-4: set_solver.
      f_equiv. f_equiv. apply wp_proper_pequiv. apply IH.
  Qed.

  Global Instance PConst_proper : Proper ((=) ==> (=) ==> (≡) ==> (≡@{prog})) PConst.
  Proof with auto.
    intros x ? <- ty ? <- A B ? C.
    mk_fresh x ({[as_var x]} ∪ prog_fvars A ∪ prog_fvars B ∪ formula_fvars C) as y.
    rewrite wp_const with (y:=y)...
    2-4: set_solver.
    rewrite wp_const with (y:=y)...
    2-4: set_solver.
    do 2 f_equiv. apply wp_proper_pequiv...
  Qed.

  Global Instance PConstList_proper : Proper ((=) ==> (=) ==> (≡) ==> (≡@{prog})) PConstList.
  Proof with auto.
    intros xs ? <- ty ? <- A B ?. induction xs as [|x xs IH].
    - simpl. apply H.
    - intros C.
      mk_fresh x ({[as_var x]} ∪ prog_fvars (PConstList xs ty A)
                    ∪ prog_fvars (PConstList xs ty B) ∪ formula_fvars C) as y.
      simpl. pose proof wp_const. simpl in H1.
      rewrite H1 with (y:=y)...
      2-4: set_solver.
      rewrite H1 with (y:=y)...
      2-4: set_solver.
      f_equiv. f_equiv. apply wp_proper_pequiv. apply IH.
  Qed.

  Global Instance PSpec_proper : Proper ((=) ==> (≡) ==> (≡) ==> (≡@{prog})) PSpec.
  Proof.
    intros w ? <- A A' ? B B' ?. unfold equiv, ffequiv in H. intros P σ.
    simpl. rewrite H. rewrite H0. done.
  Qed.

  Global Instance ref_proper : Proper ((≡@{prog}) ==> (≡@{prog}) ==> (↔)) (⊑).
  Proof.
    intros p1 p1' ? p2 p2' ?. unfold sqsubseteq, refines.
    unfold equiv, pequiv, equiv, fequiv in *.
    split; intros.
    - intros σ. intros. apply H0. apply H1. apply H. apply H2.
    - intros σ. intros. apply H0. apply H1. apply H. apply H2.
  Qed.

  Global Instance PWhile_proper : Proper ((≡) ==> (≡@{final_formula}) ==> (=) ==> (=) ==> (≡)) PWhile.
  Proof with auto.
    intros g1 g2 ? I1 I2 ? v ? <- p ? <-. intros A. simpl. unfold equiv, ffequiv in H, H0.
    do 3 f_equiv; try solve [rewrite H; rewrite H0; auto]...
    - apply wp_congr...
    - f_equiv.
      1:{ rewrite H; rewrite H0... }
      mk_fresh
        (formula_fvars I1 ∪ formula_fvars I2 ∪ formula_fvars g1
           ∪ formula_fvars g2 ∪ term_fvars v ∪ prog_fvars p)
      as x.
      rewrite wp_while_decrease_variant with (y:=x)...
      2-5: set_solver.
      rewrite wp_while_decrease_variant with (y:=x)...
      2-5: set_solver.
      rewrite H. rewrite H0...
  Qed.

  Global Instance PVar_proper_ref : Proper ((=) ==> (=) ==> (⊑) ==> (⊑)) PVar.
  Proof with auto.
    intros x ? <- ty ? <- A B ? C.
    mk_fresh x ({[as_var x]} ∪ prog_fvars A ∪ prog_fvars B ∪ formula_fvars C) as y.
    rewrite wp_var with (y:=y)...
    2-4: set_solver.
    rewrite wp_var with (y:=y)...
    2-4: set_solver.
    do 2 f_equiv. apply wp_proper_ref...
  Qed.

  Lemma pequiv_refines {p1 p2} :
    p1 ≡@{prog} p2 → p1 ⊑ p2.
  Proof. intros. intros A. specialize (H A). rewrite H. reflexivity. Qed.

  Lemma pequiv_refines_iff {p1 p2} :
    p1 ≡@{prog} p2 ↔ p1 ⊑ p2 ∧ p2 ⊑ p1.
  Proof with auto.
    split.
    - intros. split; apply pequiv_refines...
    - intros []. unfold equiv, pequiv. intros A σ. specialize (H A σ). specialize (H0 A σ).
      split; intros.
      + apply H...
      + apply H0...
  Qed.

  Lemma refines_iff_fent {p1 p2} :
    p1 ⊑ p2 ↔
      ∀ A `{!FormulaFinal A}, wp p1 A ⇛ wp p2 A.
  Proof with auto.
    intros. split; intros.
    - specialize (H (as_final_formula A)). assumption.
    - intros A. apply H...
  Qed.

  Lemma pequiv_iff_fequiv {p1 p2} :
    p1 ≡ p2 ↔
      ∀ A `{!FormulaFinal A}, wp p1 A ≡ wp p2 A.
  Proof with auto.
    intros. split; intros.
    - specialize (H (as_final_formula A)). assumption.
    - intros A. apply H...
  Qed.

  Global Instance PSeq_proper_ref : Proper ((⊑) ==> (⊑) ==> (⊑)) PSeq.
  Proof with auto.
    intros p1 p1' ? p2 p2' ?. intros A. simpl. rewrite refines_iff_fent in H.
    rewrite refines_iff_fent in H0.
    rewrite H... apply wp_congr_fent...
  Qed.

  Lemma PWhile_equiv g1 g2 I1 I2 v p1 p2 :
    g1 ≡ g2 →
    I1 ≡ I2 →
    Δ p1 = Δ p2 →
    p1 ≡ p2 →
    PWhile g1 I1 v p1 ≡ PWhile g2 I2 v p2.
  Proof with auto.
    intros. rewrite H. rewrite H0. clear H g1 H0 I1. intros A. simpl. rewrite H1.
    f_equiv. f_equiv...
    - fSimpl. unfold equiv, pequiv in H2. apply H2.
    - fSimpl.
      mk_fresh
        (formula_fvars I2 ∪ formula_fvars g2 ∪ term_fvars v ∪ prog_fvars p1 ∪ prog_fvars p2) as x.
      rewrite wp_while_decrease_variant with (y:=x)...
      2-5: set_solver.
      rewrite wp_while_decrease_variant with (y:=x)...
      2-5: set_solver.
      do 2 f_equiv.
      apply wp_proper_pequiv...
  Qed.

End semantics.
