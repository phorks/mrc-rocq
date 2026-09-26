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

Section moveme.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation sgn := (model_sgn M).

  Local Notation term := (term M).
  Local Notation formula := (formula M).
  Local Notation final_term := (final_term M).
  Local Notation final_formula := (final_formula M).

  Implicit Types (t : term).
  Implicit Types (A : formula).

  Lemma as_final_var_as_var {x : final_variable} {H} :
    @as_final_var (as_var x) H = x.
  Proof. destruct x. unfold as_final_var. simpl. f_equal. Qed.

  Global Instance term_final_pi {t} : ProofIrrel (term_final t).
  Proof.
    unfold term_final. intros p q. apply functional_extensionality_dep. intros.
    apply functional_extensionality_dep. intros H. apply eq_pi. solve_decision.
  Qed.

  Lemma as_final_term_eq {t} {t' : final_term} {H} :
    t = as_term t' →
    @as_final_term _ t H = t'.
  Proof.
    intros. subst. destruct t'. unfold as_final_term. simpl. f_equal. unfold TermFinal in H.
    apply term_final_pi.
  Qed.

  Global Instance formula_final_pi {A} : ProofIrrel (formula_final A).
  Proof.
    unfold formula_final. intros p q. apply functional_extensionality_dep. intros.
    apply functional_extensionality_dep. intros H. apply eq_pi. solve_decision.
  Qed.

  Lemma as_final_formula_eq {A} {A' : final_formula} {H} :
    A = as_formula A' →
    @as_final_formula _ A H = A'.
  Proof.
    intros. subst. destruct A'. unfold as_final_formula. simpl. f_equal. unfold FormulaFinal in H.
    apply formula_final_pi.
  Qed.

  Lemma subst_non_free A x t :
    x ∉ formula_fvars A →
    <! A[x \ t] !> = A.
  Proof with auto.
    apply subst_formula_ind with (P:=λ A B, x ∉ formula_fvars B → A = B); intros.
    - rewrite subst_af_non_free...
    - f_equiv...
    - simpl in H1. apply not_elem_of_union in H1 as [? ?].
      f_equiv; [apply H|apply H0]...
    - simpl in H1. apply not_elem_of_union in H1 as [? ?].
      f_equiv; [apply H|apply H0]...
    - reflexivity.
    - simpl in H2. apply not_elem_of_difference in H2. rewrite elem_of_singleton in H2.
      destruct H2; subst; contradiction.
  Qed.

End moveme.

Section syntax.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation sgn := (model_sgn M).

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

  (* TODO: move it near to as_var_F *)
  Definition as_var_set (vs : gset final_variable) : gset variable :=
    set_map as_var vs.

  Definition modified_vars p : gset variable := as_var_set (modified_final_vars p).
  Notation "'Δ' p" := (modified_vars p) (at level 50).

  Fixpoint prog_fvars p : gset variable :=
    match p with
    | PAsgn xs ts => (list_to_set (as_var <$> xs)) ∪ ⋃ (term_fvars ∘ as_term <$> ts)
    | PSeq p1 p2 => prog_fvars p1 ∪ prog_fvars p2
    | PIf gcs => ⋃ ((λ gcmd, prog_fvars (snd gcmd) ∪
                                 formula_fvars (as_formula (fst gcmd))) <$> gcs)
    | PWhile g inv v p => formula_fvars g ∪ formula_fvars inv ∪ term_fvars v ∪ prog_fvars p
    | PSpec w pre post => list_to_set (as_var_F w) ∪ formula_fvars pre ∪ formula_fvars post
    | PVar x _ p => prog_fvars p ∖ {[as_var x]}
    | PConst x _ p => prog_fvars p ∖ {[as_var x]}
  end.

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
                            (subst_formula post x (TVar x'))
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

  Local Notation term := (term M).

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
        f_equal. apply IHxs. set_solver.
      + apply as_final_formula_eq. apply subst_non_free. set_solver.
      + apply subst_non_free. set_solver.
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

  Fixpoint wp (p : prog) (A : formula) : formula :=
    match p with
    | PAsgn xs ts => <! A [[*$(as_var <$> xs) \ *$(as_term <$> ts)]] !>
    | PSeq p1 p2 => wp p1 (wp p2 A)
    | PIf gcs => <! ∨* ⤊(gcs.*1) ∧ ∧* $(map (λ gc, <! $(as_formula gc.1) ⇒ $(wp gc.2 A) !>) gcs) !>
    | PWhile g inv var p =>
        let var₀ := fresh_var (raw_var "") (while_fvars g inv var p) in
        <! ∀* $(set_to_list (Δ p)),
            (inv ∧ g ⇒ $(wp p inv)) ∧
            (inv ∧ ¬ g ⇒ A) ∧
            (inv ∧ g ⇒ ⌜var ∈ₜ ℕ⌝) ∧
            (∀ var₀, inv ∧ g ∧ ⌜var = var₀⌝ ⇒ $(wp p (<! ⌜var < var₀⌝ !>))) !>
    | PSpec w pre post =>
        <! pre ∧ (∀* ↑ₓ w, post ⇒ A)[_₀\ w] !>
    | PVar x ty p =>
        let x' := fresh_var x (prog_fvars p ∪ formula_fvars A) in
        <! (∀ x : ty, $(wp p <! A[x \ x'] !>))[x' \ x] !>
    | PConst x ty p =>
        let x' := fresh_var x (prog_fvars p ∪ formula_fvars A) in
        <! (∃ x : ty, $(wp p <! A[x \ x'] !>))[x' \ x] !>
    end.

 Lemma msubst_subst_comm' (A : formula) x t xs ts `{!OfSameLength xs ts} :
    x ∉ xs →
    x ∉ ⋃ (term_fvars <$> ts) →
    list_to_set xs ## term_fvars t →
    <! A[[*xs \ *ts]][x \ t] !> ≡ <! A[x \ t][[*xs \ *ts]] !>.
  Proof with auto.
    intros. rewrite <- msubst_extract_l... rewrite msubst_extract_r...
  Qed.


  Lemma wp_final {p A} :
    formula_final A →
    formula_final (wp p A).
  Proof with auto.
    generalize dependent A. induction p; intros.
    - simpl. unfold formula_final. intros. apply fvars_msubst_superset in H1.
      apply elem_of_union in H1 as [|].
      + apply (H0 _ H1).
      + set_unfold in H1. destruct H1 as (t&?&t'&->&?). apply (final_term_final t' _ H1).
    - simpl in *. apply IHp1. apply IHp2...
    - unfold formula_final. intros. simpl in H1. apply elem_of_union in H1 as [|].
      + set_unfold in H1. destruct H1 as (B&(B'&->&gc&?&?)&?). destruct gc. simpl in *.
        subst. apply (final_formula_final _ _ H3).
      + set_unfold in H1. destruct H1 as (B&(gc&->&?)&?). destruct gc. simpl in *.
        apply elem_of_union in H2 as [|].
        * apply (final_formula_final _ _ H2).
        * rewrite Forall_forall in H. unfold elem_of in H1. specialize (H (f, p) H1).
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
             unfold var_final. simpl... done.
    - eapply f_and_formula_final. Unshelve. simpl. admit.
    - simpl. unfold formula_final. intros. apply fvars_subst_superset in H0.
      apply elem_of_union in H0 as []; [|set_solver]. eapply @f_forall_formula_final with (x:=x).
      2: { apply H0. }
      clear H0. unshelve eapply f_impl_formula_final. apply IHp. intros ??.
      apply fvars_subst_superset in H0. set_unfold in H0. destruct H0.
      + apply H...
      + subst. apply fresh_var_final. typeclasses eauto.
    - simpl. unfold formula_final. intros. apply fvars_subst_superset in H0.
      apply elem_of_union in H0 as []; [|set_solver]. eapply @f_exists_formula_final with (x:=x).
      2: { apply H0. }
      clear H0. unshelve eapply f_and_formula_final. apply IHp. intros ??.
      apply fvars_subst_superset in H0. set_unfold in H0. destruct H0.
      + apply H...
      + subst. apply fresh_var_final. typeclasses eauto.
  Admitted.

  Lemma fresh_var_ne_inv y X :
    fresh_var y X ≠ y →
    y ∈ X.
  Proof with auto.
    intros. unfold fresh_var in H. induction X using set_ind_L.
    - unfold fresh_var_aux in H. destruct (decide (y ∈ ∅))... set_solver.
    - unfold fresh_var_aux in H. simpl in H. destruct (decide (y ∈ _))... set_solver.
  Qed.

  Lemma fvars_subst_superset' A x (t : term) :
    formula_fvars (<! A[x \ t] !>) ⊆ (formula_fvars A ∖ {[x]}) ∪ term_fvars t.
  Proof with auto.
    destruct (decide (x ∈ formula_fvars A)).
    - rewrite fvars_subst_free...
    - rewrite fvars_subst_non_free... set_solver.
  Qed.

  Lemma fvars_wp {p A} : formula_fvars (wp p A) ⊆ prog_fvars p ∪ formula_fvars A.
  Proof with auto.
    intros. generalize dependent A. induction p; intros; intros z; intros.
    - simpl in *. apply fvars_msubst_superset in H0.
      set_unfold in H0. destruct H0; [set_solver|]. set_unfold.
      left. right. apply elem_of_union_list. destruct H0 as (?&?&?&?&?).
      exists (term_fvars x). split... set_unfold. subst. exists x0. split...
    - simpl. simpl in H. apply IHp1 in H. set_solver.
    - simpl in *. induction gcs.
      + simpl. set_solver.
      + simpl. inversion H. subst. set_solver.
    - simpl in *. rewrite fvars_foralllist in H. simpl in *. set_unfold in H.
      destruct H. destruct_or! H.
      1-9: set_solver. destruct H. destruct_or! H.
      1-4: set_solver.
      specialize (IHp <! ⌜ v < $(fresh_var ""%string (while_fvars g inv v p)) ⌝ !>).
      apply IHp in H. set_solver.
    - simpl in *. apply elem_of_union in H as [|]; [set_solver|].
      unfold subst_initials. apply fvars_seqsubst_superset in H. apply elem_of_union in H as [|].
      + rewrite fvars_foralllist in H. simpl in H. set_solver.
      + set_solver.
    - simpl wp in H. simpl.
      pose proof (fresh_var_fresh x (prog_fvars p ∪ formula_fvars A)).
      remember (fresh_var x (prog_fvars p ∪ formula_fvars A)) as y.
      clear Heqy.
      destruct (decide (as_var x ∈ formula_fvars A)).
      + apply fvars_subst_superset' in H. set_unfold in H. destruct H; [|set_solver].
        destruct H as (?&?&?). destruct H2 as []; [done|]. apply IHp in H2.
        set_unfold in H2. destruct H2; [set_solver|]. apply fvars_subst_superset' in H2.
        set_solver.
      + pose proof (Htemp:=H). rewrite fvars_subst_non_free in H.
        * simpl in H. set_unfold in H. destruct H. destruct H; [done|].
          apply IHp in H. set_unfold in H. destruct H as []; [set_solver|].
          apply fvars_subst_superset' in H. set_unfold in H. destruct H; [set_solver|].
          subst z. apply fvars_subst_superset' in Htemp. set_solver.
        * intros ?. simpl in H1. set_unfold in H1. destruct H1. destruct H1; [done|].
          apply IHp in H1. set_unfold in H1. destruct H1; [set_solver|].
          rewrite fvars_subst_non_free in H1... set_solver.
    - simpl wp in H. simpl.
      pose proof (fresh_var_fresh x (prog_fvars p ∪ formula_fvars A)).
      remember (fresh_var x (prog_fvars p ∪ formula_fvars A)) as y.
      clear Heqy.
      destruct (decide (as_var x ∈ formula_fvars A)).
      + apply fvars_subst_superset' in H. set_unfold in H. destruct H; [|set_solver].
        destruct H as (?&?&?). destruct H2 as []; [done|]. apply IHp in H2.
        set_unfold in H2. destruct H2; [set_solver|]. apply fvars_subst_superset' in H2.
        set_solver.
      + pose proof (Htemp:=H). rewrite fvars_subst_non_free in H.
        * simpl in H. set_unfold in H. destruct H. destruct H; [done|].
          apply IHp in H. set_unfold in H. destruct H as []; [set_solver|].
          apply fvars_subst_superset' in H. set_unfold in H. destruct H; [set_solver|].
          subst z. apply fvars_subst_superset' in Htemp. set_solver.
        * intros ?. simpl in H1. set_unfold in H1. destruct H1. destruct H1; [done|].
          apply IHp in H1. set_unfold in H1. destruct H1; [set_solver|].
          rewrite fvars_subst_non_free in H1... set_solver.
  Qed.

  Local Definition k_subst p := ∀ (x : variable) (x' : final_variable) A (H :VarFinal x),
    as_var x' ∉ prog_fvars p →
    as_var x' ∉ formula_fvars A →
    <! $(wp p A)[x \ x'] !> ≡ wp (subst_prog p (@as_final_var x H) x') <! A[x \ x'] !>.

  Local Definition k_congr p := ∀ A B, A ≡ B → wp p A ≡ wp p B.

  Local Definition k_var p := ∀ x ty A (y : final_variable),
    as_var y ∉ prog_fvars p →
    as_var y ∉ formula_fvars A →
    wp (PVar x ty p) A ≡ <! (∀ x : ty, $(wp p <! A[x \ y] !>))[y \ x] !>.

  Lemma xxx p : k_var p.
  Proof with auto.
    unfold k_var. intros. simpl.
    pose proof (fresh_var_fresh x (prog_fvars p ∪ formula_fvars A)).
    remember (fresh_var x (prog_fvars p ∪ formula_fvars A)) as z.
    intros σ. pose proof (teval_total σ x) as (vx&?).
    split; intros.
    - unfold FForallT in *.
      (* pose proof (fresh_var_fresh x ({[as_var y; z]} ∪ prog_fvars p ∪ formula_fvars A)). *)
      (* remember (fresh_var x ({[as_var x; as_var y; z]} ∪ prog_fvars p ∪ formula_fvars A)) as w. *)
      (* rewrite simpl_subst_forall_rename with (y':=w). *)
      (* 2:{ admit. } *)
      (* rewrite simpl_subst_forall_rename with (y':=w) in H3. *)
      (* 2:{ admit. } *)
      (* revert H3. apply f_forall_equiv. intros. rewrite fequiv_subst_comm. *)




      rewrite feval_subst with (v:=vx)... rewrite feval_subst with (v:=vx) in H3...
      rewrite simpl_feval_fforall in *. intros vx'.
      rewrite <- feval_subst with (t:=x)...
      specialize (H3 vx').
      rewrite <- feval_subst with (t:=x) in H3...
      do 2 rewrite simpl_subst_impl in H3 |- *.
      rewrite simpl_subst_af in H3 |- *. simpl in *. rewrite simpl_feval_fimpl in H3 |- *.
      destruct (decide _); [|done]. intros. specialize (H3 H4). clear H4 e.

      subst_
      rewrite fequiv_subst_trans
      rewrite fequiv_subst_comm.
      intros. f_forall_equiv specialize (H3 H4).
      simp feval.


  Local Definition k_const p := ∀ x ty A (y : final_variable),
    as_var y ∉ prog_fvars p →
    as_var y ∉ formula_fvars A →

        <! (∀ x : ty, $(wp p <! A[x \ y] !>))[y \ x] !>
    wp (PConst x ty p) A ≡ <! ∃ x : ty, $(wp p <! A[x \ y] !>)[y \ x] !>.

  Local Lemma d_congr p : (∀ p' : prog, prog_rank p' ≤ prog_rank p → k_var p' ∧ k_const p') → k_congr p.
  Proof with auto.
    unfold k_congr. induction p using prog_strong_ind; intros.
    - simpl. rewrite H1...
    - simpl. apply IHp1; [|apply IHp2]...
      + intros. apply H... simpl. lia.
      + intros. apply H... simpl. lia.
    - simpl. f_equiv. generalize dependent B. generalize dependent A.
      induction gcs; intros; simpl... apply Forall_cons in H as [].
      rewrite H with (B:=B)...
      2: {intros. apply H0... simpl. lia. }
      f_equiv. apply IHgcs... intros. apply H0... simpl. simpl in H3. lia.
    - simpl. do 3 f_equiv. by rewrite H0.
    - simpl. by rewrite H0.
    - simpl.
      pose proof (fresh_var_fresh x (prog_fvars p ∪ formula_fvars A ∪ formula_fvars B)).
      remember (fresh_var x (prog_fvars p ∪ formula_fvars A ∪ formula_fvars B)) as z.
      assert (VarFinal z) by (subst z; typeclasses eauto).
      assert (H4:=H0). simpl in H0. forward (H0 p) by lia.
      assert (k_var p) by naive_solver. unfold k_var in H5.
      simpl in H5. rewrite H5 with (y:=as_final_var z).
      2: { rewrite as_var_as_final_var. set_solver. }
      2: { rewrite as_var_as_final_var. set_solver. }
      rewrite H5 with (y:=as_final_var z)...
      2: { rewrite as_var_as_final_var. set_solver. }
      2: { rewrite as_var_as_final_var. set_solver. }
      do 2 f_equiv. apply H...
      + intros. apply H4... simpl. lia.
      + f_equiv. exact H1.
    - simpl.
      pose proof (fresh_var_fresh x (prog_fvars p ∪ formula_fvars A ∪ formula_fvars B)).
      remember (fresh_var x (prog_fvars p ∪ formula_fvars A ∪ formula_fvars B)) as z.
      assert (VarFinal z) by (subst z; typeclasses eauto).
      assert (H4:=H0). simpl in H0. forward (H0 p) by lia.
      assert (k_const p) by naive_solver. unfold k_const in H5.
      simpl in H5. rewrite H5 with (y:=as_final_var z).
      2: { rewrite as_var_as_final_var. set_solver. }
      2: { rewrite as_var_as_final_var. set_solver. }
      rewrite H5 with (y:=as_final_var z)...
      2: { rewrite as_var_as_final_var. set_solver. }
      2: { rewrite as_var_as_final_var. set_solver. }
      do 2 f_equiv. apply H...
      + intros. apply H4... simpl. lia.
      + f_equiv. exact H1.
  Qed.

  Local Lemma d_var p : (∀ p' : prog, prog_rank p' ≤ prog_rank p → k_var p' ∧ k_const p') → k_var p.
  Proof with auto.
    unfold k_var. intros. simpl. apply f_forall_equiv. intros.
    do 2 rewrite simpl_subst_impl. rewrite simpl_subst_af. simpl. f_equiv.
    pose proof (fresh_var_fresh x (prog_fvars p ∪ formula_fvars A)).
    remember (fresh_var x (prog_fvars p ∪ formula_fvars A)) as z.


    induction p using prog_strong_ind; intros.
    1-5: admit.
    2: admit.
    simpl.
    - simpl. rewrite H1...
    - simpl. apply IHp1; [|apply IHp2]...
      + intros. apply H... simpl. lia.
      + intros. apply H... simpl. lia.
    - simpl. f_equiv. generalize dependent B. generalize dependent A.
      induction gcs; intros; simpl... apply Forall_cons in H as [].
      rewrite H with (B:=B)...
      2: {intros. apply H0... simpl. lia. }
      f_equiv. apply IHgcs... intros. apply H0... simpl. simpl in H3. lia.
    - simpl. do 3 f_equiv. by rewrite H0.
    - simpl. by rewrite H0.
    - simpl.
      pose proof (fresh_var_fresh x (prog_fvars p ∪ formula_fvars A ∪ formula_fvars B)).
      remember (fresh_var x (prog_fvars p ∪ formula_fvars A ∪ formula_fvars B)) as z.
      assert (VarFinal z) by (subst z; typeclasses eauto).
      assert (H4:=H0). simpl in H0. forward (H0 p) by lia.
      assert (k_var p) by naive_solver. unfold k_var in H5.
      simpl in H5. rewrite H5 with (y:=as_final_var z).
      2: { rewrite as_var_as_final_var. set_solver. }
      2: { rewrite as_var_as_final_var. set_solver. }
      rewrite H5 with (y:=as_final_var z)...
      2: { rewrite as_var_as_final_var. set_solver. }
      2: { rewrite as_var_as_final_var. set_solver. }
      do 2 f_equiv. apply H...
      + intros. apply H4... simpl. lia.
      + f_equiv. exact H1.
    - simpl.
      pose proof (fresh_var_fresh x (prog_fvars p ∪ formula_fvars A ∪ formula_fvars B)).
      remember (fresh_var x (prog_fvars p ∪ formula_fvars A ∪ formula_fvars B)) as z.
      assert (VarFinal z) by (subst z; typeclasses eauto).
      assert (H4:=H0). simpl in H0. forward (H0 p) by lia.
      assert (k_const p) by naive_solver. unfold k_const in H5.
      simpl in H5. rewrite H5 with (y:=as_final_var z).
      2: { rewrite as_var_as_final_var. set_solver. }
      2: { rewrite as_var_as_final_var. set_solver. }
      rewrite H5 with (y:=as_final_var z)...
      2: { rewrite as_var_as_final_var. set_solver. }
      2: { rewrite as_var_as_final_var. set_solver. }
      do 2 f_equiv. apply H...
      + intros. apply H4... simpl. lia.
      + f_equiv. exact H1.
  Qed.
    - simpl.
      pose proof (fresh_var_fresh x (prog_fvars p ∪ formula_fvars A ∪ formula_fvars B)).
      remember (fresh_var x (prog_fvars p ∪ formula_fvars A ∪ formula_fvars B)) as z.
      assert (VarFinal z) by (subst z; typeclasses eauto).
      assert (H4:=H0). simpl in H0. forward (H0 p) by lia. rewrite H0 with (y:=as_final_var z).
      2: { rewrite as_var_as_final_var. set_solver. }
      2: { rewrite as_var_as_final_var. set_solver. }
      rewrite H0 with (y:=as_final_var z)...
      2: { rewrite as_var_as_final_var. set_solver. }
      2: { rewrite as_var_as_final_var. set_solver. }
      do 2 f_equiv. apply H...
      + intros. apply H4... simpl. lia.
      + f_equiv. exact H1.
      specialize (H p eq_refl).
      forward H.
      { intros. apply H4... simpl. lia. }
      f_equiv. apply H. by rewrite H1. done.
      reflexivity.

      2: set_solver.
      j
        * f_equiv. f_equiv. admit.
        * intros. apply H0... simpl. lia.

        [reflexivity | exact Hequiv].
      + apply IHgcs...
    - simpl. f_equiv. f_equiv.
      2: { apply IHp2... intros. }
      + intros. apply H.


  Hint Extern 0 (as_final_var (as_var ?x) = ?x) => apply as_final_var_as_var : core.
  Hint Extern 0 (?x = as_final_var (as_var ?x)) => symmetry; apply as_final_var_as_var : core.
  Hint Extern 0 (as_var (as_final_var ?x) = ?x) => apply as_var_as_final_var : core.
  Hint Extern 0 (?x = as_var (as_final_var ?x)) => symmetry; apply as_var_as_final_var : core.

  Local Lemma key p : k_subst p ∧ k_congr p ∧ k_var p.
  Proof with auto.
    induction p using prog_strong_ind.
    - split_and!.
      + unfold k_subst. intros. simpl. admit.
      + admit.
      + admit.
    - admit.
      (* split_and!.  *)
      (* (* + destruct IHp1 as (?&_&_), IHp2 as (?&_&_). unfold k_subst in *; simpl in *; intros. *) *)
      (* (*   rewrite H... *) *)
    - admit.
    - admit.
    - admit.
    - assert (Hsubst : ∀ p', prog_rank p' = prog_rank p → k_subst p') by naive_solver.
      assert (Hcongr : ∀ p', prog_rank p' = prog_rank p → k_congr p') by naive_solver.
      assert (Hvar : ∀ p', prog_rank p' = prog_rank p → k_var p') by naive_solver.
      clear H. split_and!.
      + unfold k_subst. simpl. intros. rename x0 into y. destruct (decide (x = as_final_var y)).
        * subst. simpl. unfold FForallT. rewrite simpl_subst_forall_skip... do 2 f_equiv.
          remember (fresh_var (as_final_var y) _) as z1.
          remember (fresh_var (as_final_var y) _) as z2 in |- *.
          unfold k_subst in Hsubst. ospecialize (Hsubst p eq_refl z2 (as_final_var y)).
          rewrite Hsubst.
          symmetry. etrans.
          -- Set Printing Coercion. Set Printing Implicit. Unset Printing Notations.
          3:{ rewrite Hsubst. }
          rewrite <- Hsubst.


          rewrite
      + unfold k_subst, k_congr, k_var in *; destruct IHp as (Hsubst&Hcongr&Hvar); simpl; intros.
        destruct (decide (x = x0)).
        * simpl. subst. unfold FForallT. rewrite simpl_subst_forall_skip... do 2 f_equiv.

    - admit.
    - admit.




  Local Lemma key p :
    (∀ (x x' : final_variable) A,as_var x' ∉ prog_fvars p →
    as_var x' ∉ formula_fvars A →
    <! $(wp p A)[x \ x'] !> ≡ wp (subst_prog p x x') <! A[x \ x'] !>)
  ∧ (∀ A B, A ≡ B → wp p A ≡ wp p B)
  ∧ (∀ (x y : final_variable)).

  Lemma wp_congr_post {p A B} :
    A ≡ B →
    wp p A ≡ wp p B.
  Proof with auto.
    intros. induction p; simpl.
    - rewrite H...
    - admit.
    - admit.
    - admit.
    - admit.
    -

  Lemma wp_var {x ty p A} (y : final_variable) :
    as_var y ∉ prog_fvars p →
    as_var y ∉ formula_fvars A →
    wp (PVar x ty p) A ≡ <! ∀ x : ty, $(wp p <! A[x \ y] !>)[y \ x] !>.
  Proof.
    intros. simpl.
    generalize (@fresh_var_final (as_var x)
                  (prog_fvars p ∪ formula_fvars A) (@as_var_var_final x)).
    pose proof (fresh_var_fresh x (prog_fvars p ∪ formula_fvars A)).
    intros. remember (fresh_var x (prog_fvars p ∪ formula_fvars A)) as z. clear Heqz.
    f_equiv. generalize dependent A. induction p; intros.
    - simpl. rewrite msubst_subst_comm'.
      + admit.
      + admit.
      + admit.
      + admit.
    - simpl. rewrite IHp1.
    intros. simp wp. simpl.
    generalize (@fresh_var_final (as_var x) (prog_fvars p ∪ formula_fvars A) (@as_var_var_final x)).
    intros. remember (fresh_var x (prog_fvars p ∪ formula_fvars A)) as x'.
    apply f_forall_equiv. intros. do 2 rewrite simpl_subst_impl. do 2 rewrite simpl_subst_af.
    simpl. f_equiv.
    - destruct (decide (x' = x')); try done. destruct (decide (as_var y = as_var y)); try done.
    - rewrite <- wp_subst.
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

  (* Lemma wp_varlist xs p A : *)
  (*   wp <{ |[ var* xs ⦁ $p ]| }> A ≡ <! ∀* ↑ₓ xs, $(wp p A) !>. *)
  (* Proof with auto. *)
  (*   induction xs as [|x xs IH]... simpl. rewrite f_forall_ty_top. rewrite <- IH. reflexivity. *)
  (* Qed. *)

  (* Lemma wp_constlist xs p A : *)
  (*   wp <{ |[ con* xs ⦁ $p ]| }> A ≡ <! ∃* ↑ₓ xs, $(wp p A) !>. *)
  (* Proof with auto. *)
  (*   induction xs as [|x xs IH]... simpl. rewrite f_exists_ty_top. rewrite IH. reflexivity. *)
  (* Qed. *)

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
  Proof with auto.
    intros p ? <- A B H. generalize dependent B. generalize dependent A.
    induction p; intros A B Hequiv; intros; simpl; fSimpl;
      (try solve [rewrite Hequiv; reflexivity]).
    - apply IHp1. apply IHp2...
    - generalize dependent B. generalize dependent A. induction gcs; intros; simpl...
      apply Forall_cons in H as []. f_equiv.
      + rewrite H; [reflexivity | exact Hequiv].
      + apply IHgcs...
    - rewrite IHp; [reflexivity|]...
    - rewrite IHp; [reflexivity|]...
  Qed.

  Global Instance wp_proper_fent : Proper ((=) ==> (⇛) ==> (⇛)) wp.
  Proof with auto.
    intros p ? <- A B H. generalize dependent B. generalize dependent A.
    induction p; intros A B Href.
    - simpl. rewrite Href. reflexivity.
    - simpl. apply IHp1. apply IHp2. done.
    - simpl. fSimpl. induction gcs; simpl... apply Forall_cons in H as []. f_equiv.
      + rewrite H; [reflexivity | exact Href].
      + apply IHgcs...
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
    rewrite H0. unfold equiv,ffequiv in H. rewrite H. done.
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
