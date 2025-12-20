From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Strings.String.
From stdpp Require Import base gmap.
From MRC Require Import Prelude.
From MRC Require Import Stdppp.
From MRC Require Import SeqNotation.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.
From Equations Require Import Equations.

Open Scope stdpp_scope.
Open Scope refiney_scope.

Section prog.
  Context {M : model}.
  Local Notation term := (termM M).
  Local Notation final_term := (final_term (value M)).
  Local Notation formula := (formulaM M).
  Local Notation final_formula := (final_formulaM M).

  Unset Elimination Schemes.
  Inductive prog : Type :=
  | PAsgn (xs : list final_variable) (ts: list final_term) `{OfSameLength _ _ xs ts}
  | PSeq (p1 p2 : prog)
  | PIf (gcmds : list (final_formula * prog))
  | PSpec (w : list final_variable) (pre : final_formula) (post : formula)
  | PVar (x : final_variable) (p : prog)
  | PConst (x : final_variable) (p : prog).
  Set Elimination Schemes.

  Fixpoint prog_ind P :
    (∀ xs ts H, P (@PAsgn xs ts H)) →
    (∀ p1 p2, P p1 → P p2 → P (PSeq p1 p2)) →
    (∀ gcmds, Forall (λ fp, P fp.2) gcmds → P (PIf gcmds)) →
    (∀ w pre post, P (PSpec w pre post)) →
    (∀ x p, P p → P (PVar x p)) →
    (∀ x p, P p → P (PConst x p)) →
    ∀ p, P p.
  Proof with auto.
    intros Hasgn Hseq Hif Hspec Hvar Hcons. destruct p.
    - apply Hasgn.
    - apply Hseq; apply prog_ind...
    - apply Hif. induction gcmds... constructor... apply prog_ind...
    - apply Hspec.
    - apply Hvar. apply prog_ind...
    - apply Hcons. apply prog_ind...
  Qed.

  Fixpoint PVarList (xs : list final_variable) (p : prog) :=
    match xs with
    | [] => p
    | x :: xs => PVar x (PVarList xs p)
    end.

  Fixpoint PConstList (xs : list final_variable) (p : prog) :=
    match xs with
    | [] => p
    | x :: xs => PConst x (PConstList xs p)
    end.


  Notation gcmd_list := (list (final_formula * prog)).
  Definition gcmd_comprehension (gs : list final_formula) (f : final_formula → prog) : gcmd_list :=
    map (λ A, (A, f A)) gs.

  Fixpoint modified_final_vars p : gset final_variable :=
    match p with
    | PAsgn xs ts => list_to_set xs
    | PSeq p1 p2 => modified_final_vars p1 ∪ modified_final_vars p2
    | PIf gcmds => ⋃ ((modified_final_vars ∘ snd) <$> gcmds)
    | PSpec w pre post => list_to_set w
    | PVar x p => modified_final_vars p
    | PConst x p => modified_final_vars p
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
    | PIf gcmds => ⋃ ((prog_fvars ∘ snd) <$> gcmds)
    | PSpec w pre post => list_to_set (as_var_F w) ∪ formula_fvars pre ∪ formula_fvars post
    | PVar x p => prog_fvars p ∖ {[as_var x]}
    | PConst x p => prog_fvars p ∖ {[as_var x]}
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

  Fixpoint wp (p : prog) (A : formula) : formula :=
    match p with
    | PAsgn xs ts => <! A [[*$(as_var <$> xs) \ *$(as_term <$> ts)]] !>
    | PSeq p1 p2 => wp p1 (wp p2 A)
    | PIf gcs => <! ∨* ⤊(gcs.*1) ∧ ∧* $(map (λ gc, <! $(as_formula gc.1) ⇒ $(wp gc.2 A) !>) gcs) !>
    | PSpec w pre post =>
        <! pre ∧ (∀* ↑ₓ w, post ⇒ A)[_₀\ w] !>
    | PVar x p => <! ∀ x, $(wp p A) !>
    | PConst x p => <! ∃ x, $(wp p A) !>
    end.

  (* ******************************************************************* *)
  (* definition and properties of ⊑ and ≡ on progs                       *)
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

  (* ******************************************************************* *)
  (* axiomatization of recursive blocks and definition of while          *)
  (* ******************************************************************* *)
  Axiom PRec : (prog → prog) → prog.

  Axiom p_rec_unfold_l : ∀ F, PRec F ⊑ F (PRec F).
  Axiom p_rec_unfold_r : ∀ F, F (PRec F) ⊑ PRec F.

  Lemma p_rec_fixpoint : ∀ F, F (PRec F) ≡ PRec F.
  Proof.
    intros. split.
    - apply p_rec_unfold_r.
    - apply p_rec_unfold_l.
  Qed.

  Axiom p_rec_ind : ∀ F P, F P ≡ P → PRec F ⊑ P.

  (* while g => p    =    re P ⦁ if g then p; P fi er *)
  Definition PWhile (gcmds : gcmd_list) :=
    PRec (λ P, PIf gcmds).


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
    `{H : OfSameLength _ _ xs rhs} : asgn_args :=
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
    PVarList opens (PAsgn xs ts).

  Lemma PAsgnWithOpens_cons_open x xs rhs `{!OfSameLength xs rhs}
      `{!OfSameLength (x :: xs) (OpenRhsTerm :: rhs)} :
    PAsgnWithOpens (x :: xs) (OpenRhsTerm :: rhs) =
      PVar x (PAsgnWithOpens xs rhs).
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


End prog.

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

Notation "'re' p ⦁ F 'er'" := (PRec (λ p, F))
                                (in custom prog at level 95,
                                    p name, F custom prog)
    : refiney_scope.

Notation "'while' A ⟶ p 'end" :=
  (PWhile A p)
    (in custom prog at level 95,
        A custom formula, p custom prog, no associativity) : refiney_scope.

Notation "w : [ p , q ]" :=
  (PSpec w (as_final_formula p) q)
    (in custom prog at level 95, no associativity,
        w custom var_seq at level 94,
        p custom formula at level 85, q custom formula at level 85)
    : refiney_scope.

Notation ": [ p , q ]" :=
  (PSpec [] (as_final_formula p) q)
    (in custom prog at level 95, no associativity,
        p custom formula at level 85, q custom formula at level 85)
    : refiney_scope.

Notation "'|[' 'var' x '⦁' y ']|' " :=
  (PVar x y)
    (in custom prog at level 95, no associativity,
        x constr at level 0, y custom prog) : refiney_scope.

Notation "'|[' 'var*' xs '⦁' y ']|' " :=
  (PVarList xs y)
    (in custom prog at level 95, xs custom variable_list) : refiney_scope.

Notation "'|[' 'con' x '⦁' y ']|' " :=
  (PConst x y)
    (in custom prog at level 95, no associativity,
        x constr at level 0, y custom prog) : refiney_scope.

Notation "'|[' 'con*' xs '⦁' y ']|' " :=
  (PConstList xs y)
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

Section prog.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation prog := (@prog M).
  Local Notation term := (termM M).
  Local Notation formula := (formulaM M).
  Local Notation final_term := (final_termM M).
  Local Notation final_formula := (final_formulaM M).

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w : list final_variable.
  Implicit Types xs : list final_variable.

  Lemma wp_asgn xs ts A `{!OfSameLength xs ts} :
    wp <{ *xs := *$(FinalRhsTerm <$> ts) }> A ≡ <! A[[ ↑ₓ xs \ ⇑ₜ ts]] !>.
  Proof with auto.
    rewrite PAsgnWithOpens_no_opens. simpl...
  Qed.

  Lemma wp_varlist xs p A :
    wp <{ |[ var* xs ⦁ $p ]| }> A ≡ <! ∀* ↑ₓ xs, $(wp p A) !>.
  Proof with auto. induction xs as [|x xs IH]... simpl. rewrite IH. reflexivity. Qed.

  Lemma wp_constlist xs p A :
    wp <{ |[ con* xs ⦁ $p ]| }> A ≡ <! ∃* ↑ₓ xs, $(wp p A) !>.
  Proof with auto. induction xs as [|x xs IH]... simpl. rewrite IH. reflexivity. Qed.

  Global Instance PVar_proper : Proper ((=) ==> (≡) ==> (≡@{prog})) PVar.
  Proof. intros x ? <- A B ? C. simpl. rewrite (H C). reflexivity. Qed.

  Global Instance PVarList_proper : Proper ((=) ==> (≡) ==> (≡@{prog})) PVarList.
  Proof.
    intros xs ? <- A B ? C. induction xs as [|x xs IH].
    - simpl. apply H.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Global Instance PConst_proper : Proper ((=) ==> (≡) ==> (≡@{prog})) PConst.
  Proof. intros x ? <- A B ? C. simpl. rewrite (H C). reflexivity. Qed.

  Global Instance PConstList_proper : Proper ((=) ==> (≡) ==> (≡@{prog})) PConstList.
  Proof.
    intros xs ? <- A B ? C. induction xs as [|x xs IH].
    - simpl. apply H.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Global Instance wp_proper_fequiv : Proper ((=) ==> (≡) ==> (≡)) (@wp M).
  Proof with auto.
    intros p ? <- A B H. generalize dependent B. generalize dependent A.
    induction p; intros A B Hequiv; intros; simpl; fSimpl;
      (try solve [rewrite Hequiv; reflexivity]).
    - apply IHp1. apply IHp2...
    - generalize dependent B. generalize dependent A. induction gcmds; intros; simpl...
      apply Forall_cons in H as []. f_equiv.
      + rewrite H; [reflexivity | exact Hequiv].
      + apply IHgcmds...
    - rewrite IHp; [reflexivity|]...
    - rewrite IHp; [reflexivity|]...
  Qed.

  Global Instance wp_proper_pequiv {A : final_formula} : Proper ((≡@{prog}) ==> (≡)) (λ p, wp p A).
  Proof. intros p1 p2 Hp. specialize (Hp A). assumption. Qed.

End prog.
