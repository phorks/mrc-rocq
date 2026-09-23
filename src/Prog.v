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

  (* Local Notation term := (term value). *)
  Local Notation formula := (formula M).
  Local Notation final_term := (final_term M).
  Local Notation final_formula := (final_formula M).

  Unset Elimination Schemes.
  Inductive prog : Type :=
  | PAsgn (xs : list final_variable) (ts: list final_term) `{!OfSameLength xs ts}
  | PSeq (p1 p2 : prog)
  | PIf (gcmds : list (final_formula * prog))
  | PWhile (g inv : final_formula) (variant : final_term) (p : prog)
  | PSpec (w : list final_variable) (pre : final_formula) (post : formula)
  | PVar (x : final_variable) (ty : value_ty) (p : prog)
  | PConst (x : final_variable) (ty : value_ty) (p : prog).
  Set Elimination Schemes.

  Fixpoint prog_rank (p : prog) : nat :=
    match p with
    | PAsgn xs ts => 0
    | PSeq p1 p2 => 1 + max (prog_rank p1) (prog_rank p2)
    | PIf gcmds => 1 + max_list_with (prog_rank ∘ snd) gcmds
    | PWhile _ _ _ p => 1 + prog_rank p
    | PSpec w pre post => 0
    | PVar x _ p => 1 + prog_rank p
    | PConst x _ p => 1 + prog_rank p
    end.

  Fixpoint subst_prog p (x x' : final_variable) :=
    match p with
    | PAsgn xs ts => PAsgn
                       ((λ y, if (decide (y = x)) then x' else x) <$> xs)
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
                            ((λ y, if (decide (y = x)) then x else x) <$> w)
                            (as_final_formula $ subst_formula pre x (TVar x'))
                            (subst_formula post x (TVar x'))
    | PVar y ty p => if (decide (y = x))
                     then PVar y ty p
                     else PVar y ty (subst_prog p x x')
    | PConst y ty p => if (decide (y = x))
                     then PConst y ty p
                     else PConst y ty (subst_prog p x x')
  end.

  Fixpoint prog_ind P :
    (∀ xs ts H, P (@PAsgn xs ts H)) →
    (∀ p1 p2, P p1 → P p2 → P (PSeq p1 p2)) →
    (∀ gcmds, Forall (λ fp, P fp.2) gcmds → P (PIf gcmds)) →
    (∀ g inv v p, P p → P (PWhile g inv v p)) →
    (∀ w pre post, P (PSpec w pre post)) →
    (∀ x ty p, P p → P (PVar x ty p)) →
    (∀ x ty p, P p → P (PConst x ty p)) →
    ∀ p, P p.
  Proof with auto.
    intros Hasgn Hseq Hif Hwhile Hspec Hvar Hcons. destruct p.
    - apply Hasgn.
    - apply Hseq; apply prog_ind...
    - apply Hif. induction gcmds... constructor... apply prog_ind...
    - apply Hwhile. apply prog_ind...
    - apply Hspec.
    - apply Hvar. apply prog_ind...
    - apply Hcons. apply prog_ind...
  Qed.

  Lemma subst_prog_preserves_rank {p x x'} :
    prog_rank p = prog_rank (subst_prog p x x').
  Proof with auto.
    induction p; simpl; try lia.
    - induction gcmds... f_equal. simpl. inversion H. subst. rewrite H2. f_equal.
      specialize (IHgcmds H3). inversion IHgcmds...
    - destruct (decide (x0 = x)); simpl...
    - destruct (decide (x0 = x)); simpl...
  Qed.

  Fixpoint prog_rank_ind P :
    (∀ xs ts H, P (@PAsgn xs ts H)) →
    (∀ p1 p2, P p1 → P p2 → P (PSeq p1 p2)) →
    (∀ gcmds, Forall (λ fp, P fp.2) gcmds → P (PIf gcmds)) →
    (∀ g inv v p, P p → P (PWhile g inv v p)) →
    (∀ w pre post, P (PSpec w pre post)) →
    (∀ x ty p, (∀ p', prog_rank p' = prog_rank p → P p') → P (PVar x ty p)) →
    (∀ x ty p, (∀ p', prog_rank p' = prog_rank p → P p') → P (PConst x ty p)) →
    ∀ p, P p.
  Proof with auto.
    intros Hasgn Hseq Hif Hwhile Hspec Hvar Hcons. destruct p.
    - apply Hasgn.
    - apply Hseq; apply prog_rank_ind...
    - apply Hif. induction gcmds... constructor... apply prog_rank_ind...
    - apply Hwhile. apply prog_rank_ind...
    - apply Hspec.
    - apply Hvar. apply prog_rank_ind...
    - apply Hcons. intros. apply prog_rank_ind...
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
    | PIf gcmds => ⋃ ((modified_final_vars ∘ snd) <$> gcmds)
    | PWhile _ _ _ p => modified_final_vars p
    | PSpec w pre post => list_to_set w
    | PVar x _ p => modified_final_vars p ∖ {[x]}
    | PConst x _ p => modified_final_vars p ∖ {[x]}
    end.

  (* TODO: move it near to as_var_F *)
  Definition as_var_set (vs : gset final_variable) : gset variable :=
    set_map as_var vs.

  Definition modified_vars p : gset variable := as_var_set (modified_final_vars p).
  Notation "'Δ' p" := (modified_vars p) (at level 50).

  Fixpoint prog_fvars p : gset variable :=
    match p with
    | PAsgn xs ts => (list_to_set (as_var <$> xs)) ∪ ⋃ (term_fvars ∘ as_term <$> ts)
    | PSeq p1 p2 => prog_fvars p1 ∪ prog_fvars p2
    | PIf gcmds => ⋃ ((λ gcmd, prog_fvars (snd gcmd) ∪
                                 formula_fvars (as_formula (fst gcmd))) <$> gcmds)
    | PWhile g inv v p => formula_fvars g ∪ formula_fvars inv ∪ term_fvars v ∪ prog_fvars p
    | PSpec w pre post => list_to_set (as_var_F w) ∪ formula_fvars pre ∪ formula_fvars post
    | PVar x _ p => prog_fvars p ∖ {[as_var x]}
    | PConst x _ p => prog_fvars p ∖ {[as_var x]}
  end.

  Fixpoint any_guard (gcmds : gcmd_list) : formula :=
    match gcmds with
    | [] => <! true !>
    | (g, _)::cmds => <! g ∨ $(any_guard cmds) !>
    end.

  Fixpoint all_cmds (gcmds : gcmd_list) (A : formula) : formula :=
    match gcmds with
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
    PVarList opens ⊤ (PAsgn xs ts).

  Lemma PAsgnWithOpens_cons_open x xs rhs `{!OfSameLength xs rhs}
      `{!OfSameLength (x :: xs) (OpenRhsTerm :: rhs)} :
    PAsgnWithOpens (x :: xs) (OpenRhsTerm :: rhs) =
      PVar x ⊤ (PAsgnWithOpens xs rhs).
  Proof.
    simpl. unfold PAsgnWithOpens at 1. erewrite split_asgn_list_cons_open.
    unfold asgn_args_with_open. destruct (split_asgn_list xs rhs) eqn:E.
    simpl. unfold PAsgnWithOpens. rewrite E. reflexivity.
  Qed.

  Lemma PAsgnWithOpens_no_opens xs ts `{OfSameLength _ _ xs ts} :
    PAsgnWithOpens xs (FinalRhsTerm <$> ts) = PAsgn xs ts.
  Proof.
    unfold PAsgnWithOpens. rewrite split_asgn_list_no_opens. simpl. reflexivity.
  Qed.

  Lemma PAsgnWithOpens_app_nil_r xs rhs `{!OfSameLength xs rhs} {Hl} :
    @PAsgnWithOpens (xs ++ []) (rhs ++ []) Hl = PAsgnWithOpens xs rhs.
  Proof with auto.
    unfold PAsgnWithOpens.
    replace (split_asgn_list (xs ++ []) (rhs ++ [])) with (split_asgn_list xs rhs);
      [reflexivity|].
    apply rewrite_of_same_length; rewrite app_nil_r; reflexivity.
  Qed.

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
    - simpl. unfold zip_pair_elem_of. pose proof (elem_of_zip_pair_nil x (OpenRhsTerm)).
      set_solver.
    - intros. assert (Hl := of_same_length_rest H'). apply NoDup_cons in H as [].
      destruct (decide (x = l)).
      2:{ rewrite elem_of_zip_pair_hd_ne... destruct r.
          - erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
            rewrite elem_of_cons. rewrite IH... naive_solver.
          - erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
            rewrite IH... }
      subst l. destruct r.
      + erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
        rewrite elem_of_cons. rewrite IH... rewrite elem_of_zip_pair_hd... split...
      + erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
        rewrite IH... rewrite elem_of_zip_pair_hd... split; [|discriminate]. intros (i&?&?).
        simpl in H1, H2. apply elem_of_list_lookup_2 in H1. contradiction.
  Qed.

  Lemma elem_of_asgn_xs_ts x t xs rhs `{!OfSameLength xs rhs} :
    NoDup xs →
    (x, t) ∈ (asgn_xs (split_asgn_list xs rhs), asgn_ts (split_asgn_list xs rhs)) ↔
      (x, FinalRhsTerm t) ∈ (xs, rhs).
  Proof with auto.
    induction_same_length xs rhs as l r.
    - simpl. unfold zip_pair_elem_of. pose proof (elem_of_zip_pair_nil x t).
      pose proof (elem_of_zip_pair_nil x (FinalRhsTerm t)). set_solver.
    - intros. assert (Hl := of_same_length_rest H'). apply NoDup_cons in H as [].
      destruct (decide (x = l)).
      2:{ rewrite elem_of_zip_pair_hd_ne... destruct r.
          - erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open.
            rewrite asgn_ts_with_open. rewrite IH...
          - erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed.
            rewrite asgn_ts_with_closed. rewrite elem_of_zip_pair_hd_ne... }
      subst l. destruct r.
      + erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open. rewrite asgn_ts_with_open.
        rewrite IH... rewrite elem_of_zip_pair_hd... split; [|discriminate]. intros (i&?&?).
        simpl in H1, H2. apply elem_of_list_lookup_2 in H1. contradiction.
      + erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed.
        rewrite asgn_ts_with_closed. rewrite (elem_of_zip_pair_hd (FinalRhsTerm t))...
        split.
        * intros (i&?). destruct i.
          -- apply elem_of_zip_pair_hd_indexed in H1 as [_ ?]. subst...
          -- apply elem_of_zip_pair_tl_indexed in H1. apply elem_of_zip_pair_indexed_inv in H1.
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
    - apply zip_pair_Permutation_nil_inv_l in H2... destruct H2 as [-> ->]. simpl...
    - intros. apply NoDup_cons in H as []. assert (Hl:=of_same_length_rest H').
      apply zip_pair_Permutation_cons_inv_l in H1...
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
    - apply zip_pair_Permutation_nil_inv_l in H2... destruct H2 as [-> ->]. simpl...
    - intros. apply NoDup_cons in H as []. assert (Hl:=of_same_length_rest H').
      apply zip_pair_Permutation_cons_inv_l in H1...
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
        repeat erewrite asgn_ts_with_closed. rewrite zip_pair_Permutation_app_comm.
        2:{ apply asgn_of_same_length. }
        2:{ eapply of_same_length_cons. Unshelve. apply asgn_of_same_length. }
        simpl. apply zip_pair_Permutation_cons.
        1:{ apply asgn_of_same_length. }
        1:{ eapply of_same_length_app. Unshelve. all: apply asgn_of_same_length. }
        rewrite IH with (xs':=xs'1 ++ xs'0) (rhs':=ys'1 ++ ys'0)...
        2:{ apply NoDup_app in H0 as (?&?&?). apply NoDup_cons in H3 as []. apply NoDup_app.
            split_and!... intros. intros contra. apply H1 in contra. set_solver. }
        2:{ rewrite zip_pair_Permutation_app_comm... }
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

  Definition ty_ctx := gmap variable value_ty.

  Definition get_ty (Γ : ty_ctx) (x : variable) : value_ty :=
    match Γ !! x with
    | Some τ => τ
    | None => ⊤
    end.

  Local Definition while_fvars (g inv : final_formula) (var : final_term) (p : prog) :=
    formula_fvars inv ∪ formula_fvars g ∪ term_fvars var ∪ prog_fvars p.

  Fixpoint list_map {A B} (l:list A) (f: ∀ x, In x l → B) : list B.
  Proof.
    destruct l.
    - exact [].
    - forward (list_map A B l).
      + intros. apply f with (x := x). right. assumption.
      + forward (f a) by (left; reflexivity). exact (f :: list_map).
  Defined.

  (* Local Definition wp_if (gcs : list (final_formula * prog)) A (wp : ∀ gc, In gc gcs → formula) := *)
  (*   <! ∨* ⤊(gcs.*1) ∧ ∧* $(map (λ gc, <! $(as_formula gc.1) ⇒ $(wp gc _ A) !>) gcs) !>. *)

  Equations? wp (p : prog) (A : formula) : formula by wf (prog_rank p) lt :=
    wp (PAsgn xs ts) A => <! A [[*$(as_var <$> xs) \ *$(as_term <$> ts)]] !>;
    wp (PSeq p1 p2) A => wp p1 (wp p2 A);
    wp (PIf gcs) A =>
      <! ∨* ⤊(gcs.*1) ∧ ∧* $(list_map gcs (λ gc H, <! $(as_formula gc.1) ⇒ $(wp gc.2 A) !>)) !>;
    wp (PWhile g inv var p) A =>
        let var₀ :=
          fresh_var (raw_var "") (while_fvars g inv var p) in
        <! ∀* $(set_to_list (Δ p)),
            (inv ∧ g ⇒ $(wp p inv)) ∧
            (inv ∧ ¬ g ⇒ A) ∧
            (inv ∧ g ⇒ ⌜var ∈ₜ ℕ⌝) ∧
            (∀ var₀, inv ∧ g ∧ ⌜var = var₀⌝ ⇒ $(wp p (<! ⌜var < var₀⌝ !>))) !>;
    wp (PSpec w pre post) A =>
        <! pre ∧ (∀* ↑ₓ w, post ⇒ A)[_₀\ w] !>;
    wp (PVar x ty p) A =>
      let x' := as_final_var (fresh_var x (formula_fvars A)) in
      <! ∀ x' : ty, $(wp (subst_prog p x x') A) !>;
    wp (PConst x ty p) A =>
        let x' := as_final_var (fresh_var x (formula_fvars A)) in
        <! ∃ x' : ty, $(wp (subst_prog p x x') A) !>.
  Proof with auto.
    all: try lia.
    - clear wp. induction gcs.
      + simpl in H. destruct H.
      + simpl in H. simpl. destruct H.
        * subst. simpl. lia.
        * specialize (IHgcs H). lia.
    - simpl. pose proof (@subst_prog_preserves_rank _ p x x'). lia.
    - simpl. pose proof (@subst_prog_preserves_rank _ p x x'). lia.
  Qed.

  Lemma wp_if {gcs A} :
    wp (PIf gcs) A =
      <! ∨* ⤊(gcs.*1) ∧ ∧* $(map (λ gc, <! $(as_formula gc.1) ⇒ $(wp gc.2 A) !>) gcs) !>.
  Proof with auto.
    simp wp. f_equal. induction gcs... simpl.
    - simpl. f_equal...
  Qed.

  (* TODO: move these *)
  Lemma seqsubst_extract_l (A : formula) x t xs ts `{!OfSameLength xs ts} :
    x ∉ xs →
    x ∉ ⋃ (term_fvars <$> ts) →
    list_to_set xs ## term_fvars t →
    <! A[;x, *xs \ t, *ts;] !> ≡ <! A[x \ t][;*xs \ *ts;] !>.
  Proof with auto.
    intros. simpl.
    induction_same_length xs ts as y u...
    intros. simpl. unfold OfSameLength in H'. simpl in H'. inversion H'.
    apply not_elem_of_cons in H as []. rewrite <- IH...
    2-3: set_solver.
    rewrite fequiv_subst_comm...
    - f_equiv. f_equiv. f_equiv. apply eq_pi. solve_decision.
    - set_solver.
    - set_solver.
  Qed.

  Lemma seqsubst_extract_r (A : formula) x t xs ts `{!OfSameLength xs ts} :
    <! A[;x, *xs \ t, *ts;] !> ≡ <! A[;*xs \ *ts;][x \ t] !>.
  Proof with auto. intros. simpl. repeat f_equiv. apply eq_pi. solve_decision. Qed.

  Lemma seqsubst_subst_comm (A : formula) x t xs ts `{!OfSameLength xs ts} :
    x ∉ xs →
    x ∉ ⋃ (term_fvars <$> ts) →
    list_to_set xs ## term_fvars t →
    <! A[;*xs \ *ts;][x \ t] !> ≡ <! A[x \ t][;*xs \ *ts;] !>.
  Proof with auto.
    intros. rewrite <- seqsubst_extract_l... rewrite seqsubst_extract_r. reflexivity.
  Qed.

  Lemma msubst_subst_comm' (A : formula) x t xs ts `{!OfSameLength xs ts} :
    x ∉ xs →
    x ∉ ⋃ (term_fvars <$> ts) →
    list_to_set xs ## term_fvars t →
    <! A[[*xs \ *ts]][x \ t] !> ≡ <! A[x \ t][[*xs \ *ts]] !>.
  Proof with auto.
    intros. rewrite <- msubst_extract_l... rewrite msubst_extract_r...
  Qed.

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
    - simpl. unfold as_var_set. induction gcmds.
      + simpl. set_solver.
      + simpl in *. rewrite set_map_union. apply union_subseteq. split.
        * apply union_subseteq_l'. inversion H. subst. etrans; [exact H2|set_solver].
        * apply union_subseteq_r'. etrans.
          -- apply IHgcmds. inversion H. set_solver.
          -- set_solver.
    - simpl. unfold as_var_set. set_solver.
    - unfold as_var_set. simpl. do 2 apply union_subseteq_l'. induction w; set_solver.
    - simpl. set_solver.
    - simpl. set_solver.
  Qed.

  (* TODO: move it *)
  Lemma elem_of_set_to_list {x} {X : gset variable} :
    x ∈ set_to_list X ↔ x ∈ X.
  Proof with auto.
    unfold elem_of at 1. split; intros.
    - induction X using set_ind_L.
      + rewrite set_to_list_empty in H. inversion H.
      + rewrite set_to_list_union_singleton_l_perm in H... set_solver.
    - induction X using set_ind_L.
      + set_solver.
      + rewrite set_to_list_union_singleton_l_perm... set_solver.
  Qed.

  (* Local Lemma f_wp_if {A B C D : formula} : *)
  (*   <! (A ∨ B) ∧ ((A ⇒ C) ∨ D) !> ≡ <! (A ∧ C) ∨ (B ∧ D) !>. *)
  (* Proof with auto. *)
  (*   (* rewrite f_impl_as_not_and. rewrite f_not_and. rewrite f_not_stable. *) *)
  (*   intros σ. destruct (feval_lem σ A). *)
  (*   - split; intros. *)
  (*     + simp feval. simp feval in H0. destruct H0. destruct H1... *)
  (*       * left. rewrite simpl_feval_fimpl in H1... *)
  (*       *  *)
  (*     + simp feval. split... simp feval in H0. *)
  (*   - split; intros. *)
  (*     + simp feval in *. destruct H0. destruct H1... *)
  (*     + simp feval in *. destruct H0. *)
  (*       * *)
  (*     + simp feval. simp feval in H0. destruct H0. *)
  (*       * split_and!... *)

  (* Local Lemma wp_if_cons_alt {g : final_formula} {c gcs A} : *)
  (*   wp (PIf ((g, c) :: gcs)) A ≡ <! (g ∧ $(wp c A)) ∨ $(wp (PIf gcs) A) !>. *)
  (* Proof. *)
  (*   intros σ. simpl. destruct (feval_lem σ g). *)
  (*   - split; intros. *)
  (*     +  *)

  (* Local Lemma wp_if_cons {g : final_formula} {c gcs A B} : *)
  (*   <! $(wp c A) !> ≡ <! $(wp c B) !> → *)
  (*   Forall (λ fp, wp fp.2 A ≡ wp fp.2 B) gcs → *)
  (*   wp_if ((g, c) :: gcs) A ≡ wp_if ((g, c) :: gcs) B. *)
  (* Proof with auto. *)
  (*   intros. unfold wp_if. simpl. do 2 f_equiv... *)
  (*   1:{ rewrite H... } *)
  (*   induction gcs... simpl. inversion H0. subst. rewrite H3. f_equiv... *)
  (* Qed. *)

  (* TODO: move this important lemma *)
  Lemma fvar_equiv {x} {t : term} {A B : formula} :
    x ∉ formula_fvars A →
    A ≡ B →
    <! B[x \ t] !> ≡ B.
  Proof with auto.
    intros. trans A... rewrite <- fequiv_subst_non_free with (A:=A) (x:=x) (t:=t)...
    f_equiv...
  Qed.

  Lemma fresh_var_final {x X} :
    var_final x →
    var_final (fresh_var x X).
  Proof with auto.
    unfold var_final. intros. unfold fresh_var. generalize dependent x. induction (size X); intros.
    - simpl. destruct (decide (x ∈ X))...
    - simpl in *. destruct (decide (x ∈ X))...
  Qed.

  Lemma wp_final {p A} :
    formula_final A →
    formula_final (wp p A).
  Proof with auto.
    generalize dependent A. induction p using prog_rank_ind; intros.
    - simp wp in *. unfold formula_final. intros. apply fvars_msubst_superset in H1.
      apply elem_of_union in H1 as [|].
      + apply (H0 _ H1).
      + set_unfold in H1. destruct H1 as (t&?&t'&->&?). apply (final_term_final t' _ H1).
    - simp wp in *.
    - rewrite wp_if. unfold formula_final. intros. simpl in H1. apply elem_of_union in H1 as [|].
      + set_unfold in H1. destruct H1 as (B&(B'&->&gc&?&?)&?). destruct gc. simpl in *.
        subst. apply (final_formula_final _ _ H3).
      + set_unfold in H1. destruct H1 as (B&(gc&->&?)&?). destruct gc. simpl in *.
        apply elem_of_union in H2 as [|].
        * apply (final_formula_final _ _ H2).
        * unfold elem_of in H1. rewrite Forall_forall in H. specialize (H (f, p) H1).
          simpl in H. specialize (H A H0). apply H...
    - simp wp in *. apply FForallList_final. eapply f_and_formula_final. Unshelve.
      + unfold FImpl. eapply f_or_formula_final. Unshelve. apply IHp. apply final_formula_final...
      + eapply f_and_formula_final. Unshelve.
        * unfold FImpl. eapply f_or_formula_final. Unshelve. apply H.
        * eapply f_and_formula_final. Unshelve. eapply f_forall_formula_final. Unshelve.
          unfold FImpl. eapply f_or_formula_final. Unshelve.
          apply IHp. unfold formula_final. intros. simpl in H0. apply elem_of_union in H0 as [|].
          -- apply (final_term_final _ _ H0).
          -- set_unfold. destruct H0; [| contradiction]. subst. apply fresh_var_final.
             unfold var_final. simpl...
          (* -- eapply f_not_formula_final. Unshelve. eapply f_and_formula_final. Unshelve. *)
          (*    eapply f_and_formula_final. Unshelve. intros x ?. simpl in H0. *)
          (*    apply elem_of_union in H0 as [|]. *)
          (*    ++ apply (final_term_final v _ H0). *)
          (*    ++ set_unfold in H0. subst. by apply fresh_var_final. *)
          (* -- apply IHp. intros x ?. simpl in H0. apply elem_of_union in H0 as [|]. *)
          (*    ++ apply (final_term_final v _ H0). *)
          (*    ++ set_unfold in H0. destruct H0; [|contradiction]. subst. by apply fresh_var_final. *)
    - eapply f_and_formula_final. Unshelve. admit.
    - simp wp in *. eapply f_forall_formula_final. Unshelve. unfold FImpl.
      eapply f_or_formula_final. Unshelve. apply H.
    - eapply f_exists_formula_final. Unshelve. eapply f_and_formula_final.
      Unshelve. apply IHp...
  Admitted.


  Lemma wp_congr_post {p A B} :
    A ≡ B →
    wp p A ≡ wp p B.
  Proof with auto.
    intros H. generalize dependent B. generalize dependent A.
    induction p; intros A B Hequiv; intros; simpl; fSimpl;
      (try solve [rewrite Hequiv; reflexivity]).
    - apply IHp1. apply IHp2...
    - generalize dependent B. generalize dependent A. induction gcmds; intros; simpl...
      apply Forall_cons in H as []. f_equiv.
      + rewrite H; [reflexivity | exact Hequiv].
      + apply IHgcmds...
    - f_equiv. apply IHp...
    - f_equiv. apply IHp...
  Qed.

  Lemma fvars_wp {x : final_variable} {p A} :
    as_var x ∉ prog_fvars p →
    as_var x ∉ formula_fvars A →
    as_var x ∉ formula_fvars (wp p A).
  Proof with auto.
    intros. generalize dependent A. induction p; intros.
    - simpl. simpl in H. intros contra. apply fvars_msubst_superset in contra.
      set_unfold in contra. destruct contra; [done|]. set_unfold in H.
      apply H. right. apply elem_of_union_list. destruct H2 as (?&?&?&?&?).
      exists (term_fvars x0). split... set_unfold. subst. exists x1. split...
    - simpl. apply IHp1; set_solver.
    - simpl in *. induction gcmds.
      + simpl. set_solver.
      + simpl. inversion H0. subst. set_solver.
    - simpl. rewrite fvars_foralllist. simpl. set_unfold. intros contra. destruct contra.
      destruct_or! H1.
      1-9: set_solver. destruct H1. destruct_or! H1.
      1-4: set_solver.
      forward IHp by set_solver.
      ospecialize (IHp <! ⌜ v < $(fresh_var ""%string (while_fvars g inv v p)) ⌝ !> _).
      + simpl. set_solver.
      + done.
    - simpl in *. intros contra. apply elem_of_union in contra as [|]; [set_solver|].
      unfold subst_initials. apply fvars_seqsubst_superset in H1. apply elem_of_union in H1 as [|].
      + rewrite fvars_foralllist in H1. simpl in H1. set_solver.
      + set_solver.
    - set_solver.
    - set_solver.
  Qed.

  Lemma not_elem_of_prog_fvars_if_inv {x gcs} :
    x ∉ prog_fvars (PIf gcs) →
    (∀ (g : final_formula) p, (g, p) ∈ gcs → x ∉ formula_fvars g ∧ x ∉ prog_fvars p).
  Proof with auto.
    simpl. intros. apply Decidable.not_or. intros contra. apply H.
    apply elem_of_union_list. exists (prog_fvars p ∪ formula_fvars g). set_unfold.
    split.
    - exists (g, p)...
    - destruct contra...
  Qed.

  (* Lemma wp_subst {p : prog} {x} {A : formula} (y : final_variable) : *)
  (*   as_var x ∉ prog_fvars p → *)
  (*   as_var y ∉ prog_fvars p → *)
  (*   as_var y ∉ formula_fvars A → *)
  (*   <! $(wp p  A) [x \ y] !> ≡ wp p <! A [x \ y] !>. *)
  (* Proof with auto. *)
  (*   intros Hpx Hpy Hfy. generalize dependent A. induction p; intros A Hfy. *)
  (*   - simpl in *. rewrite msubst_subst_comm'... *)
  (*     + apply not_elem_of_union in Hpx as [? _]. apply not_elem_of_list_to_set in H0... *)
  (*     + apply not_elem_of_union in Hpx as [_ ?]. intros contra. set_unfold in contra. *)
  (*       apply H0. clear H0. destruct contra as (t&?&(t'&?&?)). *)
  (*       apply elem_of_union_list. exists (term_fvars t). split... *)
  (*       apply elem_of_list_fmap. exists t'. split... simpl. subst... *)
  (*     + set_solver. *)
  (*   - simpl. rewrite IHp1... *)
  (*     2-3: set_solver. *)
  (*     + apply wp_congr_post. simpl in Hpx, Hpy. apply IHp2; set_solver. *)
  (*     + apply fvars_wp... set_solver. *)
  (*   - simpl. rewrite simpl_subst_and. f_equiv. *)
  (*     + clear H. *)
  (*       pose proof (not_elem_of_prog_fvars_if_inv Hpx) as Hx. *)
  (*       pose proof (not_elem_of_prog_fvars_if_inv Hpy) as Hy. *)
  (*       rewrite fequiv_subst_non_free... clear Hpx Hpy. set_unfold. *)
  (*       intros (_&(B'&->&(gc&?&?))&?). subst. destruct gc. simpl in *. *)
  (*       specialize (Hx f p H0) as []... *)
  (*     + induction gcmds... simpl. *)
  (*       pose proof (not_elem_of_prog_fvars_if_inv Hpx) as Hx. *)
  (*       pose proof (not_elem_of_prog_fvars_if_inv Hpy) as Hy. *)
  (*       rewrite simpl_subst_and. f_equiv. *)
  (*       * rewrite simpl_subst_impl. f_equiv. *)
  (*         -- apply fequiv_subst_non_free. ospecialize (Hx a.1 a.2 _). *)
  (*            ++ apply elem_of_cons. left. destruct a... *)
  (*            ++ destruct Hx... *)
  (*         -- rewrite Forall_forall in H. apply H... *)
  (*            ++ left. *)
  (*            ++ ospecialize (Hx a.1 a.2 _); [destruct a; left|]. destruct Hx... *)
  (*            ++ ospecialize (Hy a.1 a.2 _); [destruct a; left|]. destruct Hy... *)
  (*       * clear Hx Hy. apply IHgcmds; clear IHgcmds. *)
  (*         -- inversion H... *)
  (*         -- intros contra. set_solver. *)
  (*         -- set_solver. *)
  (*   - simpl. rewrite simpl_subst_foralllist. *)
  (*     2:{ intros contra. apply elem_of_set_to_list in contra. *)
  (*         unfold modified_vars in contra. apply modified_vars_subseteq_fvars in contra. *)
  (*         set_solver. } *)
  (*     2:{ intros z ??. rewrite list_to_set_set_to_list in H. *)
  (*         apply modified_vars_subseteq_fvars in H. set_solver. } *)
  (*     f_equiv. *)
  (*     rewrite simpl_subst_and. f_equiv. *)
  (*     1:{ rewrite simpl_subst_impl. rewrite fequiv_subst_non_free by set_solver. *)
  (*         rewrite IHp by set_solver. f_equiv. apply wp_congr_post. *)
  (*         rewrite fequiv_subst_non_free by set_solver... } *)
  (*     rewrite simpl_subst_and. f_equiv. *)
  (*     1:{ rewrite simpl_subst_impl. rewrite fequiv_subst_non_free by set_solver. *)
  (*         f_equiv. } *)
  (*     rewrite simpl_subst_and. f_equiv. *)
  (*     1:{ rewrite simpl_subst_impl. rewrite fequiv_subst_non_free by set_solver. *)
  (*         f_equiv. rewrite fequiv_subst_non_free by set_solver... } *)
  (*     pose proof (fresh_var_fresh ""%string (while_fvars g inv v p)). *)
  (*     remember (fresh_var ""%string (while_fvars g inv v p)) as z. *)
  (*     admit. *)
  (*   - simpl. rewrite simpl_subst_and. f_equiv. *)
  (*     + apply fequiv_subst_non_free. set_solver. *)
  (*     + unfold subst_initials. rewrite seqsubst_subst_comm... *)
  (*       * rewrite simpl_subst_foralllist. *)
  (*         -- rewrite simpl_subst_impl. rewrite fequiv_subst_non_free... set_solver. *)
  (*         -- set_unfold. intros (x'&?&?). apply as_var_inj in H. subst x. apply Hpx. *)
  (*            apply elem_of_union. left. apply elem_of_union. left. *)
  (*            apply elem_of_list_to_set. set_solver. *)
  (*         -- simpl. set_solver. *)
  (*       * set_unfold. intros (x'&?&?). set_solver. *)
  (*       * set_solver. *)
  (*       * set_solver. *)
  (*   - simpl. unfold FForallT. destruct (decide (x0 = x)). *)
  (*     + subst. rewrite simpl_subst_forall_skip... f_equiv. f_equiv.  *)
  (*     rewrite simpl_subst_forall. *)
  (*     + f_equiv. rewrite simpl_subst_impl. rewrite fequiv_subst_non_free. *)
  (*       * rewrite IHp... *)
  (*         -- simpl in Hpx. *)
  (*     rewrite simpl_subst_forall. adm *)
  (*     2:{ unfold while_fvars in H. intros contra. unfold quant_subst_fvars in contra. *)
  (*         apply elem_of_union in contra as [|]. *)
  (*         - set_solver. *)
  (*         set_solver. *)
  (*     rewrite  *)
  (*            ++ *)
  (*               ** destruct a. left. *)



  (*       rewrite Forall_forall in H. *)
  (*       apply (Hx f p)...  *)

  (*       set_unfold in goal. rewrite fvars_orlist. set_unfold. *)

  (*       simpl in *. set_unfold in Hpx. app *)



  (*     f_equiv. induction gcmds. *)
  (*     + simpl. rewrite simpl_subst_and. do 2 rewrite simpl_subst_af. simpl... *)
  (*     + simpl. rewrite simpl_subst_and. fSimpl. admit. *)
  (*   - simpl. rewrite simpl_subst_foralllist. *)
  (*     2:{ admit. } *)
  (*     2:{ admit. } *)

  (*       * rewrite fequiv_subst_non_free... simpl. simpl in Hpx. apply not_elem_of_union. *)
  (*         split; [set_solver|]. rewrite fvars_orlist. set_unfold in Hpx. *)
  (*         intros contra. apply Hpx. right. apply elem_of_union_list in contra as (?&?&?). *)
  (*         apply elem_of_union_list. set_unfold in H0. destruct H0 as (?&?&?&?&?&?&?). *)
  (*         exists (prog_fvars x3.2 ∪ formula_fvars x3.1). *)
  (*         subst. split... 2: set_solver. set_unfold. exists x3. split... *)
  (*       * rewrite simpl_subst_and. f_equiv. *)
  (*         -- rewrite simpl_subst_impl. f_equiv. *)
  (*            ++ rewrite fequiv_subst_non_free... simpl in Hpx. set_solver. *)
  (*            ++ inversion H. subst. rewrite H2... all: set_solver. *)
  (*         -- *)
  (*         split... set_unfold. *)
  (*         exists x0. *)
  (*       simpl. *)
  (*       apply elem_of_ *)
  (*       set_unfold. *)
  (*       simpl in H0. *)
  (*       unfold *)

  (* Local Lemma notin_while_fvars_inv {x : variable} {g inv var p A}: *)
  (*   x ∉ while_fvars g inv var p A → *)
  (*   (x ∉ formula_fvars g ∧ *)
  (*      x ∉ formula_fvars inv ∧ *)
  (*      x ∉ term_fvars var ∧ *)
  (*      x ∉ prog_fvars p ∧ *)
  (*      x ∉ formula_fvars A). *)
  (* Proof. unfold while_fvars. set_solver. Qed. *)

  (* Lemma wp_while_fvar (x : variable) {g inv var p A} : *)
  (*   x ∉ while_fvars g inv var p → *)
  (*   wp (PWhile g inv var p) A ≡ *)
  (*       <! ∀* $(set_to_list (Δ p)), *)
  (*           (inv ∧ g ⇒ $(wp p inv)) ∧ *)
  (*           (inv ∧ ¬ g ⇒ A) ∧ *)
  (*           (inv ∧ g ⇒ ⌜var ∈ₜ ℕ⌝) ∧ *)
  (*           (∀ x, inv ∧ g ∧ ⌜var = x⌝ ⇒ $(wp p (<! ⌜var < x⌝ !>))) !>. *)
  (* Proof with auto. *)
  (*   intros Hx. simpl. *)
  (*   pose proof (fresh_var_fresh ""%string (while_fvars g inv var p)) as Hy. *)
  (*   remember (fresh_var (raw_var "") (while_fvars g inv var p)) as y. *)
  (*   do 4 f_equiv. intros σ. split; intros H. *)
  (*   - rewrite simpl_feval_fforall in H. rewrite simpl_feval_fimpl. intros. *)
  (*     simp feval in H0. destruct H0 as (?&?&?). simpl in H2. destruct H2 as (xv&?&?). *)
  (*     specialize (H xv). rewrite simpl_subst_impl in H. rewrite simpl_feval_fimpl in H. *)
  (*     forward H. *)
  (*     + do 2 rewrite simpl_subst_and. *)
  (*       unfold while_fvars in Hy. do 2 rewrite fequiv_subst_non_free by set_solver. *)
  (*       rewrite simpl_subst_af. simpl. destruct (decide (y = y)); [| contradiction]. *)
  (*       rewrite subst_term_non_free by set_solver. simp feval. split_and!... simpl. *)
  (*       exists xv. split... *)
  (*     + *)
  (*     { *)

  (*     } *)
  (*   - do 2 f_equiv. intros σ. *)


  (* ******************************************************************* *)
  (* definition and properties of ⊑ and ≡ on prog                        *)
  (* ******************************************************************* *)
  Global Instance refines : SqSubsetEq prog := λ p1 p2,
    ∀ A : final_formula, wp p1 A ⇛ (wp p2 A).

  Global Instance pequiv : Equiv prog := λ p1 p2, ∀ A : final_formula, wp p1 A ≡ wp p2 A.
  Global Instance refines_refl : Reflexive refines.
  Proof with auto. intros ??.  reflexivity. Qed.

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

  Lemma wp_asgn xs ts A `{!OfSameLength xs ts} :
    wp <{ *xs := *$(FinalRhsTerm <$> ts) }> A ≡ <! A[[ ↑ₓ xs \ ⇑ₜ ts]] !>.
  Proof with auto.
    rewrite PAsgnWithOpens_no_opens. simpl...
  Qed.

  Lemma f_hastype_unknown t :
    <! ⌜t ∈ₜ ⊤⌝ !> ≡ <! true !>.
  Proof with auto.
    intros σ. split; intros _; [done|]. destruct (teval_total σ t) as [v Hv].
    simp feval. simpl. exists v. split... apply hastype_unknown.
  Qed.

  Lemma f_forall_ty_top x A :
    <! ∀ x : ⊤, A !> ≡ <! ∀ x, A !>.
  Proof. unfold FForallT. rewrite f_hastype_unknown. fSimpl. Qed.

  Lemma f_exists_ty_top x A :
    <! ∃ x : ⊤, A !> ≡ <! ∃ x, A !>.
  Proof. unfold FExistsT. rewrite f_hastype_unknown. fSimpl. Qed.

  Lemma wp_varlist xs p A :
    wp <{ |[ var* xs ⦁ $p ]| }> A ≡ <! ∀* ↑ₓ xs, $(wp p A) !>.
  Proof with auto.
    induction xs as [|x xs IH]... simpl. rewrite f_forall_ty_top. rewrite IH. reflexivity.
  Qed.

  Lemma wp_constlist xs p A :
    wp <{ |[ con* xs ⦁ $p ]| }> A ≡ <! ∃* ↑ₓ xs, $(wp p A) !>.
  Proof with auto.
    induction xs as [|x xs IH]... simpl. rewrite f_exists_ty_top. rewrite IH. reflexivity.
  Qed.

  Global Instance PVar_proper : Proper ((=) ==> (=) ==> (≡) ==> (≡@{prog})) PVar.
  Proof. intros x ? <- ty ? <- A B ? C. simpl. rewrite (H C). reflexivity. Qed.

  Global Instance PVarList_proper : Proper ((=) ==> (=) ==> (≡) ==> (≡@{prog})) PVarList.
  Proof.
    intros xs ? <- ty ? <- A B ? C. induction xs as [|x xs IH].
    - simpl. apply H.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Global Instance PConst_proper : Proper ((=) ==> (=) ==> (≡) ==> (≡@{prog})) PConst.
  Proof. intros x ? <- ty ? <- A B ? C. simpl. rewrite (H C). reflexivity. Qed.

  Global Instance PConstList_proper : Proper ((=) ==> (=) ==> (≡) ==> (≡@{prog})) PConstList.
  Proof.
    intros xs ? <- ty ? <- A B ? C. induction xs as [|x xs IH].
    - simpl. apply H.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Global Instance wp_proper_fequiv : Proper ((=) ==> (≡) ==> (≡)) wp.
  Proof with auto. intros p ? <- A B. exact wp_congr_post. Qed.

  Global Instance wp_proper_fent : Proper ((=) ==> (⇛) ==> (⇛)) wp.
  Proof with auto.
    intros p ? <- A B H. generalize dependent B. generalize dependent A.
    induction p; intros A B Href.
    - simpl. rewrite Href. reflexivity.
    - simpl. apply IHp1. apply IHp2. done.
    - simpl. fSimpl. induction gcmds; simpl... apply Forall_cons in H as []. f_equiv.
      + rewrite H; [reflexivity | exact Href].
      + apply IHgcmds...
    - simpl. rewrite Href. done.
    - simpl. rewrite Href. done.
    - simpl. rewrite IHp; [reflexivity|]...
    - simpl. rewrite IHp; [reflexivity|]...
  Qed.

  Global Instance wp_proper_pequiv {A : final_formula} : Proper ((≡@{prog}) ==> (≡)) (λ p, wp p A).
  Proof. intros p1 p2 Hp. specialize (Hp A). assumption. Qed.

  Global Instance PSpec_proper : Proper ((=) ==> (≡) ==> (≡) ==> (≡@{prog})) PSpec.
  Proof.
    intros w ? <- A A' ? B B' ?. unfold equiv, ffequiv in H. intros P σ.
    simpl. rewrite H. rewrite H0. done.
  Qed.

  Global Instance ref_proper : Proper ((≡@{prog}) ==> (≡@{prog}) ==> (↔)) (⊑).
  Proof.
    intros p1 p1' ? p2 p2' ?. unfold sqsubseteq, refines. unfold equiv, pequiv, equiv, fequiv in *.
    split; intros.
    - intros σ. intros. apply H0. apply H1. apply H. apply H2.
    - intros σ. intros. apply H0. apply H1. apply H. apply H2.
  Qed.

  Global Instance PWhile_proper : Proper ((≡) ==> (≡@{final_formula}) ==> (=) ==> (=) ==> (≡)) PWhile.
  Proof.
    intros g1 g2 ? I1 I2 ? v ? <- p ? <-. intros A. simpl. unfold equiv,ffequiv in H0.
    rewrite H0. unfold equiv, ffequiv in H. rewrite H. do 4 f_equiv. apply f_forall_equiv.
    intros.
  Qed.

  Global Instance PVar_proper_ref : Proper ((=) ==> (=) ==> (⊑) ==> (⊑)) PVar.
  Proof. intros x ? <- ty ? <- A B ? C. simpl. rewrite (H C). reflexivity. Qed.


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

  Lemma fequiv_fent_iff {A B : formula} :
    A ≡ B ↔ A ⇛ B ∧ B ⇛ A.
  Proof with auto.
    split.
    - intros. split; intros σ; apply H.
    - intros []. split; intros...
  Qed.

  (*
    The type of [wp p] must be [final_formula → final_formula]. The current definition has two
    limitations that has forced us to define it as [formula → formula] but the notions of
    equivalence and refinement are limited to only final formulas. This prevents us from defining
    proper instances for some constructors like [PSeq] and [PWhile]. The two limitations are
    as follows:
    1. PWhile: [var₀] is chosen explicitly as an initial variable. Currently we do this to ensure
        the chosen new variable is fresh in [inv], [g], [var], and [A]; otherwise it might capture
        an existing variable. Another benefit of the current approach is that [var₀] doesn't
        depent on [p]. This allows to prove for example [wp_proper_fequiv] easily.
      . The correct and tricky way of doing it is to pick a [fresh_var] out
        of the union of the free variables of all these and also UNIVERSALLY QUANTIFY over it to
        ensure no unintentional capture happens.
        The new variable must also be fresh in [p]. (No concept currently corresponds to the set
        of free variables of a program; prog_fvars doesn't work: e.g., it must consider the free
        variables in rhs terms of an assignment.)
    2. PSpec: [post] can contain initial variables. We currently only substitute initial versions
        of frame variables. This approach allows treating this operation as a regular substitution.
        A correct approach is to find ALL initial variables inside post and replace them.
        A new function [initial_vars_of : formula → gset variable] is required for this reason.
    For the time being, to avoid complicating proofs, and also benefit from the proper instances
    for sequential composition and iteration, we assume totality of [pequiv] as an axiom.
   *)
  Axiom refines_total : ∀ {p1 p2}, p1 ⊑ p2 → (∀ (A : formula), wp p1 A ⇛ wp p2 A).

  Lemma pequiv_total  : ∀ {p1 p2}, p1 ≡ p2 → (∀ (A : formula), wp p1 A ≡ wp p2 A).
  Proof with auto.
    intros. apply fequiv_fent_iff. apply pequiv_refines_iff in H as []. split;
      apply refines_total...
  Qed.

  Global Instance PSeq_proper_ref : Proper ((⊑) ==> (⊑) ==> (⊑)) PSeq.
  Proof with auto.
    intros p1 p1' ? p2 p2' ?. intros A σ ?. simpl in *. apply @refines_total with (p1:=p1)...
    pose proof (wp_proper_fent p1 p1 eq_refl (wp p2 A) (wp p2' A)). apply H2...
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
    - fSimpl. pose proof (pequiv_total H2). apply H.
  Qed.


  Lemma r_while_body {g I v p1 p2} :
    Δ p1 = Δ p2 →
    p1 ⊑ p2 →
    PWhile g I v p1 ⊑ PWhile g I v p2.
  Proof with auto.
    intros. intros A. simpl. rewrite H. f_equiv. f_equiv...
    - fSimpl. apply refines_total...
    - fSimpl. apply refines_total...
  Qed.

End semantics.
