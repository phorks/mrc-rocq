From Stdlib Require Import Lists.List. Import ListNotations.
From Equations Require Import Equations.
From stdpp Require Import base tactics listset gmap.
(* From Stdlib Require Import Strings.String. *)
From MRC Require Import Prelude.
From MRC Require Import SeqNotation.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.
From MRC Require Import Prog.

(*TODO: move it, probably the non-prime one is useless *)
Instance feval_proper_fent' {M σ} : Proper ((@fent M) ==> impl) (feval σ).
Proof.
  intros A B H H0. apply H. apply H0.
Qed.

Definition of_same_length_eq_l {A B} {l1 l1' : list A} {l2 : list B} (H : OfSameLength l1 l2) :
  l1 = l1' →
  OfSameLength l1' l2.
Proof. intros. subst. exact H. Qed.

Definition of_same_length_eq_r {A B} {l1 : list A} {l2 l2' : list B} (H : OfSameLength l1 l2) :
  l2 = l2' →
  OfSameLength l1 l2'.
Proof. intros. subst. exact H. Qed.

Definition of_same_length_eq {A B} {l1 l1' : list A} {l2 l2' : list B} (H : OfSameLength l1 l2) :
  l1 = l1' →
  l2 = l2' →
  OfSameLength l1' l2'.
Proof. intros. subst. exact H. Qed.

Open Scope stdpp_scope.
Open Scope refiney_scope.

(* TODO: move it *)
#[global] Hint Unfold universal_relation : core.
(* Lemma lookup_list_to_map_zip_cons_ne {K A} `{Countable K} *)
(*     (ks : list K) (xs : list A) (k : K) (x : A) (i : K) `{OfSameLength K A ks xs} : *)
(*   k ≠ i → *)
(*   (list_to_map (zip (k :: ks) (x ::xs)) : gmap K A) !! i = *)
(*     (list_to_map (zip ks xs) : gmap K A) !! i. *)
(* Proof with auto. *)
(*   intros. simpl. rewrite lookup_insert_ne... *)
(* Qed. *)
(* Proof with auto. *)
(*   remember (length ks) as n eqn:E. symmetry in E. generalize dependent xs. *)
(*   generalize dependent ks. induction n; intros. *)
(*   - simpl. apply length_zero_iff_nil in E. subst. simpl in H1. rewrite lookup_empty in H1. *)
(*     discriminate. *)
(*   - assert (E1:=E). rewrite of_same_length in E1. *)
(*     apply length_nonzero_iff_cons in E as (k'&ks'&->&?). *)
(*     apply length_nonzero_iff_cons in E1 as (x'&xs'&->&?). subst. simpl in H1. *)
(*     destruct (decide (k' = k)). *)
(*     + subst. rewrite lookup_insert in H1. exists 0. simpl. split... *)
(*     + forward (IHn ks') by reflexivity. forward (IHn xs'). *)
(*       { unfold OfSameLength... } *)
(*       rewrite lookup_insert_ne in H1... destruct (IHn H1) as (i&?&?). *)
(*       exists (S i). simpl. split... *)
(* Qed. *)

Section refinement.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation prog := (@prog M).
  Local Notation term := (term value).
  Local Notation formula := (formula value).
  Local Notation final_term := (final_term value).

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w : list final_variable.
  Implicit Types xs : list final_variable.
  (* Implicit Types ts : list term. *)


  Lemma r_strengthen_post w pre post post' `{FormulaFinal _ pre} :
    post' ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros Hent A Hinit. simpl. f_simpl. rewrite <- Hent. reflexivity.
  Qed.

  Lemma r_weaken_pre w pre pre' post `{FormulaFinal _ pre} `{FormulaFinal _ pre'} :
    pre ⇛ pre' ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre', post] }>.
  Proof.
    intros Hent A Hinit. simpl. f_simpl. assumption.
  Qed.

  (* TODO: move it *)
  Lemma teval_delete_bottom_state_var σ x t v :
    x ∉ dom σ →
    teval (<[x:=value_bottom M]> σ) t v ↔ teval σ t v.
  Proof with auto.
    intros. generalize dependent v. induction t; intros.
    - split; inversion 1...
    - split; inversion 1; subst x1.
      + destruct (decide (x = x0)).
        * subst x0. rewrite (lookup_total_insert σ) in H2. subst v0. constructor.
          rewrite (lookup_total_alt σ). apply (not_elem_of_dom σ) in H. rewrite H.
          simpl...
        * rewrite (lookup_total_insert_ne σ) in H2...
      + destruct (decide (x = x0)).
        * subst x0 v0. rewrite (lookup_total_alt σ) in H2. apply (not_elem_of_dom σ) in H.
          rewrite H in H2. simpl in H2. rewrite H2. constructor.
          rewrite (lookup_total_insert σ)...
        * constructor. rewrite (lookup_total_insert_ne σ)...
    - split; inversion 1; subst; apply TEval_App with (vargs:=vargs)...
      + clear H1 H6. generalize dependent vargs. induction args; intros.
        * inversion H4. subst. constructor.
        * inversion H4. subst. constructor.
          -- rewrite <- H0... left...
          -- apply IHargs... intros. apply H0. right...
      + clear H1 H6. generalize dependent vargs. induction args; intros.
        * inversion H4. subst. constructor.
        * inversion H4. subst. constructor.
          -- rewrite H0... left...
          -- apply IHargs... intros. apply H0. right...
  Qed.

  Lemma afeval_delete_bottom_state_var σ x af :
    x ∉ dom σ →
    afeval (<[x:=value_bottom M]> σ) af ↔ afeval σ af.
  Proof with auto.
    intros. destruct af...
    - simpl. setoid_rewrite teval_delete_bottom_state_var...
    - simpl. split; intros (vargs&?&?); exists vargs; split; auto; clear H1;
        generalize dependent vargs; induction args; intros; inversion H0; subst;
        try constructor...
      + rewrite <- (teval_delete_bottom_state_var _ x a v)...
      + rewrite (teval_delete_bottom_state_var _ x a v)...
  Qed.

  Lemma feval_delete_bottom_state_var σ x A :
    x ∉ dom σ →
    feval (<[x:=value_bottom M]> σ) A ↔ feval σ A.
  Proof with auto.
    intros. induction A; simp feval.
    2-5: naive_solver.
    apply afeval_delete_bottom_state_var...
  Qed.

  Lemma f_exists_introduce_binder x A :
    A ⇛ <! ∃ x, A !>.
  Proof with auto.
    intros σ H. simp feval. pose proof (teval_total σ x) as [v Hv].
    exists v. rewrite feval_subst with (v:=v)... inversion Hv.
    subst x0. subst v0. unfold state in *.
    rewrite lookup_total_alt in H1. destruct (σ !! x) eqn:E.
    + simpl in H1. subst. rewrite insert_id...
    + simpl in H1. rewrite <- H1. rewrite feval_delete_bottom_state_var...
      apply (not_elem_of_dom σ)...
  Qed.

  Lemma f_forall_drop_binder A x :
    <! ∀ x, A !> ⇛ A.
  Proof with auto.
    unfold FForall. apply f_ent_contrapositive. rewrite f_not_stable.
    apply f_exists_introduce_binder.
  Qed.

  (* Definition x := raw_var "x". *)
  (* Definition y := raw_var "y". *)
  (* Definition n2 := raw_var "2". *)
  (* Definition n5 := raw_var "5". *)

  (* Definition FSForall xs A := <! ∀* xs, A[[*xs \ ]] *)

  (* Infix "⇛ₗ@{ M }" := (@fent M _) (at level 70, only parsing, no associativity) *)
  (*     : refiney_scope. *)
  (* Lemma play : *)
  (*   @fent M *)
  (*   <! ∀* $([y; x]), ⌜x = y + n2⌝ !> <! ⌜y = n5 + n2⌝ !>. *)
  (* Proof. *)
  (*   simpl. rewrite f_forall_elim with (t:=n5). *)
  (*   rewrite f_forall_elim with (t:=y). *)
  (*   rewrite simpl_subst_af. simpl. rewrite simpl_subst_af. simpl. *)
  (*   simpl. *)
  (*   unfold formula_subst. *)
  (*   cbn. unfold quant_subst_skip_cond. *)
  (*   simpl. *)
  (*   simpl. hnf. *)
  Lemma teval_var_term_map_det {σ} m mv mv' :
    @teval_var_term_map M σ m mv →
    @teval_var_term_map M σ m mv' →
    mv = mv'.
  Proof with auto.
    intros. generalize dependent m. generalize dependent mv'.
    induction mv as [| x v mv Hx IH] using map_ind; intros.
    - destruct H as []. destruct H0 as []. rewrite <- H in H0. rewrite dom_empty_L in H0.
      apply dom_empty_inv_L in H0. subst...
    - assert (Hmv:=H). assert (Hmv':=H0). destruct H as []. destruct H0 as [].
      rewrite dom_insert_L in H. symmetry in H. rewrite H in H0.
      apply dom_union_inv_L in H as (m1&m2&?&?&?&?).
      2: { apply disjoint_singleton_l. apply not_elem_of_dom... }
      apply dom_singleton_inv_L in H4 as [t Ht]. subst m1.
      rewrite <- insert_union_singleton_l in H. subst m. rename m2 into m.
      apply dom_union_inv_L in H0 as (m1&m2&?&?&?&?).
      2: { apply disjoint_singleton_l. apply not_elem_of_dom... }
      apply dom_singleton_inv_L in H4 as [v' Hv']. subst m1.
      rewrite <- insert_union_singleton_l in H. subst mv'. rename m2 into mv'.
      assert (teval σ t v).
      { apply H1 with (x:=x); apply lookup_insert... }
      assert (teval σ t v').
      { apply H2 with (x:=x); apply lookup_insert... }
      clear H1 H2. pose proof (teval_det _ _ _ H H4) as ->. clear H H4.
      apply (teval_var_term_map_delete x) in Hmv, Hmv'.
      apply map_disjoint_singleton_l in H3, H0. rewrite (delete_insert) in Hmv, Hmv'...
      rewrite (delete_insert) in Hmv, Hmv'... rewrite (IH mv' m)...
  Qed.

  Lemma teval_var_term_map_zip_cons_inv σ x (xs : list variable) t ts mv `{OfSameLength _ _ xs ts} :
    NoDup (x :: xs) →
    @teval_var_term_map M σ (to_var_term_map (x :: xs) (t :: ts)) mv →
    ∃ v mv', teval σ t v ∧ mv = {[x := v]} ∪ mv' ∧ x ∉ dom mv'
             ∧ @teval_var_term_map M σ (to_var_term_map xs ts) mv'.
  Proof with auto.
    intros. generalize dependent mv. generalize dependent ts. generalize dependent t.
    generalize dependent x. induction xs as [|x' xs' IH]; intros; assert (Hl:=H).
    - apply of_same_length_nil_inv_l in Hl as ->. unfold to_var_term_map in H1. simpl in H1.
      destruct H1 as []. rewrite insert_empty in H1. rewrite dom_singleton_L in H1.
      apply dom_singleton_inv_L in H1 as [v ->]. exists v, ∅. split_and!.
      + eapply H2; [apply lookup_insert|apply lookup_singleton].
      + rewrite map_union_empty...
      + apply not_elem_of_empty.
      + hnf. cbn. split... intros. apply lookup_empty_Some in H1 as [].
    - apply of_same_length_cons_inv_l in Hl as (t'&ts'&->&?).
      apply NoDup_cons in H0 as []. forward (IH x')...
      apply of_same_length_rest in H as Hl. specialize (IH t' ts' Hl).
      destruct H1 as []. unfold to_var_term_map in H1. rewrite dom_list_to_map_zip_L in H1.
      2:{ typeclasses eauto. } rewrite list_to_set_cons in H1.
      apply dom_union_inv_L in H1 as (m1&m2&?&?&?&?).
      2: { set_solver. }
      apply dom_singleton_inv_L in H6 as [v Hv]. subst m1.
      rewrite <- insert_union_singleton_l in H1. subst mv. rename m2 into mv.
      assert (teval_var_term_map σ (to_var_term_map (x' :: xs') (t' :: ts')) mv).
      { split.
        - unfold to_var_term_map. rewrite dom_list_to_map_zip_L...
        - intros. assert (x0 ≠ x).
          { intros contra. subst. apply elem_of_dom_2 in H6. rewrite H7 in H6.
            apply elem_of_list_to_set in H6. contradiction. }
          apply (H4 x0)...
          ++ unfold to_var_term_map. simpl. rewrite lookup_insert_ne...
          ++ rewrite lookup_insert_ne...
      }
      destruct (IH mv) as (v'&mv'&?&?&?&?)...
      exists v, mv. split_and!...
      + apply (H4 x).
          * unfold to_var_term_map. simpl. rewrite lookup_insert...
          * rewrite lookup_insert...
        + rewrite insert_union_singleton_l...
        + set_solver.
  Qed.

  Lemma f_existslist_as_foralllist (xs : list variable) A :
    <! ∃* xs, A !> ≡ <! ¬ ∀* xs, ¬ A !>.
  Proof with auto.
    induction xs as [|x xs IH]; simpl...
    - rewrite f_not_stable...
    - intros σ. unfold FForall. rewrite IH... rewrite f_not_stable...
  Qed.
  (* Lemma f_exists_intro_as_ssubst A (xs : list variable) ts `{OfSameLength _ _ xs ts} : *)
  (*   length xs ≠ 0 → *)
  (*   NoDup xs → *)
  (*   <! A[[*xs \ *ts]] !> ⇛ <! ∃* xs, A !>. *)
  (* Proof with auto. *)
  (*   generalize dependent ts. generalize dependent A. *)
  (*   induction xs as [|x xs IH]; intros; assert (Hl:=H). *)
  (*   1: { simpl in H0. contradiction. } *)
  (*   apply of_same_length_cons_inv_l in Hl as (t&ts'&->&?). rename ts' into ts. *)
  (*   clear H0. destruct (length xs) eqn:E. *)
  (*   1:{ apply length_zero_iff_nil in E, H2. subst. simpl in *. rewrite (ssubst_single A x t). *)
  (*       apply f_exists_intro... } *)
  (*   apply of_same_length_rest in H as ?. clear E. simpl. assert (Hunique:=H1). *)
  (*   apply NoDup_cons in H1 as []. rewrite f_exists_existslist_comm. *)
  (*   intros σ ?. pose proof (teval_total σ t) as [vt Hvt]. *)
  (*   rewrite f_exists_intro with (t:=TConst vt). *)
  (*   specialize (IH <! A[x \ $(TConst vt)] !> ts H0). forward IH by lia. *)
  (*   rewrite IH in H4... rewrite <- ssubst_extract_inside in H4... *)
  (*   2: { simpl. set_solver. } *)
  (*   pose proof (teval_var_term_map_total σ (to_var_term_map (x::xs) (t::ts))) as (mv&?). *)
  (*   rewrite feval_simult_subst with (mv:=mv)... *)
  (*   pose proof (teval_var_term_map_total σ (to_var_term_map (x::xs) ((TConst vt)::ts))) as (mv'&?). *)
  (*   rewrite feval_simult_subst with (mv:=mv') in H4... *)
  (*   enough (mv = mv') by (subst mv'; assumption). clear H2 IH H4 A. *)
  (*   apply of_same_length_rest in H as Hl. *)
  (*   apply teval_var_term_map_zip_cons_inv with (H:=Hl) in H5 as (v&mv0&?&->&?&?)... *)
  (*   apply teval_var_term_map_zip_cons_inv with (H:=Hl) in H6 as (v'&mv1&?&->&?&?)... *)
  (*   inversion H6. subst v0. subst v'. pose proof (teval_det t vt v Hvt H2) as ->. *)
  (*   pose proof (teval_var_term_map_det _ _ _ H5 H8) as ->... *)
  (* Qed. *)
  Lemma f_foralllist_elim_as_ssubst A (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    length xs ≠ 0 →
    NoDup xs →
    <! ∀* xs, A !> ⇛ <! A[[*xs \ *ts]] !>.
  Proof with auto.
    generalize dependent ts. generalize dependent A.
    induction xs as [|x xs IH]; intros; assert (Hl:=H).
    1: { simpl in H0. contradiction. }
    apply of_same_length_cons_inv_l in Hl as (t&ts'&->&?). rename ts' into ts.
    clear H0. destruct (length xs) eqn:E.
    1:{ apply length_zero_iff_nil in E, H2. subst. simpl in H1. rewrite (ssubst_single A x t).
        apply f_forall_elim... }
    apply of_same_length_rest in H as ?. clear E. simpl. assert (Hunique:=H1).
    apply NoDup_cons in H1 as []. rewrite f_forall_foralllist_comm.
    intros σ ?. pose proof (teval_total σ t) as [vt Hvt].
    rewrite f_forall_elim with (t:=TConst vt) in H4.
    specialize (IH <! A[x \ $(TConst vt)] !> ts H0). forward IH by lia.
    rewrite IH in H4... rewrite <- ssubst_extract_inside in H4...
    2: { simpl. set_solver. }
    pose proof (teval_var_term_map_total σ (to_var_term_map (x::xs) (t::ts))) as (mv&?).
    rewrite feval_simult_subst with (mv:=mv)...
    pose proof (teval_var_term_map_total σ (to_var_term_map (x::xs) ((TConst vt)::ts))) as (mv'&?).
    rewrite feval_simult_subst with (mv:=mv') in H4...
    enough (mv = mv') by (subst mv'; assumption). clear H2 IH H4 A.
    apply of_same_length_rest in H as Hl.
    apply teval_var_term_map_zip_cons_inv with (H:=Hl) in H5 as (v&mv0&?&->&?&?)...
    apply teval_var_term_map_zip_cons_inv with (H:=Hl) in H6 as (v'&mv1&?&->&?&?)...
    inversion H6. subst v0. subst v'. pose proof (teval_det t vt v Hvt H2) as ->.
    pose proof (teval_var_term_map_det _ _ _ H5 H8) as ->...
  Qed.

  Lemma simpl_ssubst_not A (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (¬ A) [[*xs \ *ts]] !> ≡ <! ¬ (A [[*xs \ *ts]]) !>.
  Proof. simp simult_subst. reflexivity. Qed.
  Lemma simpl_ssubst_and A B (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (A ∧ B) [[*xs \ *ts]] !> ≡ <! A [[*xs \ *ts]] ∧ B [[*xs \ *ts]] !>.
  Proof. simp simult_subst. reflexivity. Qed.
  Lemma simpl_ssubst_or A B (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (A ∨ B) [[*xs \ *ts]] !> ≡ <! A [[*xs \ *ts]] ∨ B [[*xs \ *ts]] !>.
  Proof. simp simult_subst. reflexivity. Qed.
  Lemma simpl_ssubst_impl A B (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (A ⇒ B) [[*xs \ *ts]] !> ≡ <! A [[*xs \ *ts]] ⇒ B [[*xs \ *ts]] !>.
  Proof. unfold FImpl. simp simult_subst. reflexivity. Qed.
  Lemma simpl_ssubst_iff A B (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (A ⇔ B) [[*xs \ *ts]] !> ≡ <! A [[*xs \ *ts]] ⇔ B [[*xs \ *ts]] !>.
  Proof. unfold FIff, FImpl. simp simult_subst. reflexivity. Qed.

  Lemma f_exists_intro_as_ssubst A (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    length xs ≠ 0 →
    NoDup xs →
    <! A[[*xs \ *ts]] !> ⇛ <! ∃* xs, A !>.
  Proof with auto.
    intros. rewrite f_existslist_as_foralllist. rewrite <- f_ent_contrapositive.
    rewrite f_not_stable. rewrite <- simpl_ssubst_not. apply f_foralllist_elim_as_ssubst...
  Qed.

  Lemma initial_free_in_final_formula x A :
    formula_final A →
    initial_var_of x ∉ formula_fvars A.
  Proof.
    intros. intros contra. apply H in contra. cbv in contra. discriminate.
  Qed.

  Lemma r_contract_frame (x : final_variable) pre post `{FormulaFinal _ pre} :
    <{ x : [pre, post] }> ⊑ <{ : [pre, post[₀x\x] ] }>.
  Proof with auto.
    intros A Hfree. simpl. f_simpl. rewrite f_forall_drop_binder.
    unfold subst_initials. simpl. rewrite simpl_subst_impl.
    rewrite fequiv_subst_non_free with (A:=A).
    - reflexivity.
    - apply initial_free_in_final_formula...
  Qed.

  Lemma f_existslist_app (xs1 xs2 : list variable) A :
    <! ∃* $(xs1 ++ xs2), A !> ≡ <! ∃* xs1, ∃* xs2, A !>.
  Proof with auto.
    induction xs1 as [|x1 xs1 IH]... simpl. rewrite IH...
  Qed.

  Lemma f_foralllist_app (xs1 xs2 : list variable) A :
    <! ∀* $(xs1 ++ xs2), A !> ≡ <! ∀* xs1, ∀* xs2, A !>.
  Proof with auto.
    induction xs1 as [|x1 xs1 IH]... simpl. rewrite IH...
  Qed.

  Lemma f_foralllist_drop_binders (xs : list variable) A :
    <! ∀* xs, A !> ⇛ <! A !>.
  Proof with auto.
    induction xs as [|x xs IH]; simpl.
    - reflexivity.
    - rewrite IH. rewrite f_forall_drop_binder. reflexivity.
  Qed.

  Lemma f_existslist_introduce_binders (xs : list variable) A :
    <! A !> ⇛ <! ∃* xs, A !>.
  Proof with auto.
    rewrite f_existslist_as_foralllist. rewrite <- f_ent_contrapositive. rewrite f_not_stable.
    apply f_foralllist_drop_binders.
  Qed.

  Lemma f_eqlist_app ts1 ts1' ts2 ts2'
                          `{OfSameLength _ _ (ts1 ++ ts1') (ts2 ++ ts2')}
                          `{OfSameLength _ _ ts1 ts2}
                          `{OfSameLength _ _ ts1' ts2'} :
    <! ⌜$(ts1 ++ ts1') =* $(ts2 ++ ts2')⌝ !> ≡@{formula}
       <! ⌜$(ts1) =* $(ts2)⌝ ∧ ⌜$(ts1') =* $(ts2')⌝ !>.
  Proof with auto.
    generalize dependent ts2.
    induction ts1 as [|t1 ts1 IH]; simpl; intros; assert (Hl:=H0).
    - apply of_same_length_nil_inv_l in Hl as ->. simpl. rewrite f_eqlist_nil.
      f_simpl. f_equiv. apply OfSameLength_pi.
    - apply of_same_length_cons_inv_l in Hl as (t2&ts2''&->&?). rename ts2'' into ts2.
      simpl. repeat rewrite f_eqlist_cons. rewrite <- f_and_assoc. f_simpl.
      rewrite IH... Unshelve.
      + simpl in H. apply of_same_length_rest in H...
      + apply of_same_length_rest in H0...
  Qed.

  Lemma f_eqlist_replace_l ts1 ts1' ts2 {H : OfSameLength ts1 ts2} (Heq : ts1 = ts1') :
    @FEqList _ ts1 ts2 H ≡@{formula} @FEqList _ ts1' ts2 (of_same_length_eq_l H Heq).
  Proof. subst. f_equiv. apply OfSameLength_pi. Qed.

  Lemma f_eqlist_replace_r ts1 ts2 ts2' {H : OfSameLength ts1 ts2} (Heq : ts2 = ts2') :
    @FEqList _ ts1 ts2 H ≡@{formula} @FEqList _ ts1 ts2' (of_same_length_eq_r H Heq).
  Proof. subst. f_equiv. apply OfSameLength_pi. Qed.

  Lemma f_eqlist_replace {ts1 ts1' ts2 ts2'} {H : OfSameLength ts1 ts2} :
    ∀ Heq1 : ts1 = ts1',
    ∀ Heq2 : ts2 = ts2',
    @FEqList _ ts1 ts2 H ≡@{formula} @FEqList _ ts1' ts2' (of_same_length_eq H Heq1 Heq2).
  Proof. intros. subst. f_equiv. apply OfSameLength_pi. Qed.

(* Ltac split_eqlist_fmap_app l1 l2 f g := *)
(*   repeat match goal with *)
(*     | H : context[@FEqList (f <$> l1 ++ l2) (f <$> l1 ++ l2) ?Hlength] |- _ => *)
(*         rewrite (@f_eqlist_fmap_app _ l1 l2 ?f ?g ?Hlength _ _) in H *)
(*     | |- context[@FEqList (f <$> l1 ++ l2) (g <$> l1 ++ l2) ?Hlength] => *)
(*         assert (True); *)
(*         rewrite (@f_eqlist_fmap_app _ l1 l2 ?f ?g ?Hlength _ _) *)
(*     | |- context[FEqList (?f <$> ?l1) ?l2] => *)
(*         let H := fresh in *)
(*         idtac f l1 *)
(*     end. *)


Notation "' xs" := (TVar ∘ as_var <$> xs : list term)
                       (in custom term at level 0,
                           xs constr at level 0) : refiney_scope.
Notation "'₀ xs" := (TVar ∘ initial_var_of <$> xs : list term)
                       (in custom term at level 0,
                           xs constr at level 0) : refiney_scope.
  Lemma subst_initials_seqsubst_lists_unique xs :
    @seqsubst_lists_unique M (initial_var_of <$> xs) (TVar ∘ as_var <$> xs).
  Proof.
    unfold seqsubst_lists_unique. intros.
    rewrite elem_of_list_pair_indexed in H0, H1. destruct H0 as []. destruct H1 as [].
    apply list_lookup_fmap_inv in H0 as (x1&?&?).
    apply list_lookup_fmap_inv in H1 as (x2&?&?).
    apply list_lookup_fmap_inv in H2 as (x3&?&?).
    apply list_lookup_fmap_inv in H3 as (x4&?&?).
    rewrite H4 in H6. inversion H6. subst x3. rewrite H5 in H7.
    inversion H7. subst x4. clear H6 H7. rewrite H0 in H1.
    rewrite H2. rewrite H3. f_equal. apply initial_var_of_inj in H1. assumption.
  Qed.

  Lemma subst_initials_vars_terms_disjoin xs :
    list_to_set (initial_var_of <$> xs) ## ⋃ (@term_fvars value <$> (TVar ∘ as_var <$> xs)).
  Proof.
    (* Set Printing Coercions. Unset Printing Notations. *)
    intros x0 H1 H2. set_unfold. destruct H1 as (x&?&?). subst.
    apply elem_of_union_list in H2 as (fvars&?&?).
    apply elem_of_list_fmap in H as (x1&?&?). apply elem_of_list_fmap in H2 as (x2&?&?).
    subst x1. simpl in H. subst fvars. apply elem_of_singleton in H1.
    apply initial_var_of_eq_final_variable in H1 as [].
  Qed.

  Hint Resolve subst_initials_seqsubst_lists_unique : core.
  Hint Resolve subst_initials_vars_terms_disjoin : core.

  Lemma fold_subst_initials A w :
    seqsubst A (initial_var_of <$> w) (TVar ∘ as_var <$> w) = <! A[_₀\ w] !>.
  Proof. reflexivity. Qed.

  Lemma seqsubst_non_free A (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    formula_fvars A ## list_to_set xs →
    <! A[; *xs \ *ts ;] !> ≡ A.
  Proof with auto.
    generalize dependent ts. induction xs as [|x xs IH]; intros; assert (Hl:=H).
    - apply of_same_length_nil_inv_l in Hl as ->. simpl...
    - apply of_same_length_cons_inv_l in Hl as (t&ts'&->&?). rename ts' into ts. simpl...
      rewrite IH.
      2:{ set_solver. }
      rewrite fequiv_subst_non_free... set_solver.
  Qed.

  Lemma f_drop_subst_initials A w :
    formula_final A →
    <! A[_₀\ w] !> ≡ A.
  Proof.
    intros. unfold subst_initials. apply seqsubst_non_free. intros x0 ? ?.
    set_unfold. destruct H1 as (x&?&?). apply H in H0. unfold var_final in H0.
    rewrite H1 in H0. simpl in H0. discriminate.
  Qed.


  Lemma r_assignment w xs pre post ts `{FormulaFinal _ pre} `{OfSameLength _ _ xs ts} :
    length xs ≠ 0 →
    NoDup xs →
    <! ⌜'₀w =* 'w⌝ ∧ ⌜'₀xs =* 'xs⌝ ∧ pre !> ⇛ <! post[[ *$(as_var <$> xs) \ *$(as_term <$> ts) ]] !> ->
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs := *$(FinalRhsTerm <$> ts)  }>.
  Proof with auto.
    intros Hlength Hnodup proviso A Hfinal. simpl. rewrite wp_asgn.
    assert (<! pre !> ≡ <! pre [_₀\w ++ xs] !>) as ->.
    { rewrite f_drop_subst_initials... }
    rewrite <- simpl_subst_initials_and. rewrite fmap_app.
    unfold subst_initials. rewrite <- f_foralllist_one_point...
    rewrite f_foralllist_app. rewrite (f_foralllist_drop_binders (as_var <$> w)).
    rewrite (f_foralllist_elim_as_ssubst <! post ⇒ A !> _ (as_term <$> ts))...
    2:{ rewrite length_fmap... }
    2:{ apply NoDup_fmap... apply as_var_inj. }
    erewrite f_eqlist_replace. Unshelve.
    4: { do 2 rewrite fmap_app. do 2 rewrite <- list_fmap_compose. reflexivity. }
    3: { rewrite fmap_app. reflexivity. }
    rewrite f_eqlist_app. rewrite f_impl_dup_hyp. rewrite (f_and_assoc _ pre).
    rewrite f_and_assoc in proviso. rewrite proviso. clear proviso. rewrite simpl_ssubst_impl.
    f_simpl. rewrite <- f_eqlist_app.
    erewrite f_eqlist_replace. Unshelve.
    5: { rewrite <- fmap_app. rewrite list_fmap_compose. reflexivity. }
    3: { rewrite <- fmap_app. reflexivity. }
    pose proof (@f_foralllist_one_point M
                  (initial_var_of <$> (w ++ xs)) ((TVar ∘ as_var <$> (w++xs)))) as ->...
    rewrite fold_subst_initials. rewrite f_drop_subst_initials.
    2: { unfold formula_final. intros. apply fvars_ssubst_superset in H1.
         set_unfold. destruct H1.
         - apply Hfinal...
         - apply elem_of_union_list in H1 as (fvars&?&?).
           apply elem_of_list_fmap in H1 as (t&->&?).
           apply elem_of_list_fmap in H1 as (t'&->&?).
           pose proof (final_term_final t').
           apply H3... }
    reflexivity.
  Qed.

    rewrite H1... rewrite simult_subst_
    2: {  }

    Set Printing Coercions.
    rewrite f_foralllist_one_point.
    4: { do 2 rewrite fmap_app. do 2 rewrite <- list_fmap_compose. reflexivity. }
    3: { rewrite fmap_app. reflexivity. }
    2:{ rewrite length_fmap... }
    2:{ apply NoDup_fmap... apply as_var_inj. }
    erewrite f_eqlist_replace. Unshelve.
    rewrite f_foralllist_impl_unused_r.
    rewrite f_impl_elim.
    f_impl_elim
    rewrite <- f_and_assoc at 2.
    rewrite proviso.
    Unshelve.
    pose proof (fmap_app ((@TVar value) ∘ as_var) w xs).
    assert (OfSameLength (initial_var_of <$> w ++ xs) ((@TVar value) ∘ as_var <$> w ++ xs) =
 OfSameLength (initial_var_of <$> w ++ xs) ((TVar ∘ as_var <$> w) ++ ((@TVar value) ∘ as_var <$> xs))).
    { rewrite H1. reflexivity. }
    Unset Printing Notations. Set Printing Implicit.
    rewrite simpl_ssubst_impl.
    split_eqlist_fmap_app w xs (initial_var_of) ((@TVar (value)) ∘ as_var).

    clear.
    pose proof (f_eqlist_fmap_app w xs (initial_var_of) (TVar ∘ as_var)).
    unfold fmap.
    rewrite H1.

    assert (<! ⌜@*(initial_var_of <$> w ++ xs) =* $(fmap (TVar ∘ as_var) (w ++ xs))⌝
              ⇒ pre ∧ (∀* $(fmap as_var (w ++ xs)),  post ⇒ A) !> ⇛
            <! ⌜@*(initial_var_of <$> w ++ xs) =* $(fmap (TVar ∘ as_var) (w ++ xs))⌝
            ⇒ post[[ *$(as_var <$> xs) \ *$(as_term <$> ts)]]
              ∧ (∀* $(fmap as_var (w ++ xs)),  post ⇒ A) !> ).
    { admit. }
    rewrite H1. clear H1.



    assert
      (<! ⌜₀x = x⌝ ⇒ (pre ∧ (∀ x, post ⇒ A)) !> ⇛
                                <! ⌜₀x = x⌝ ⇒ (post [x \ t] ∧ (∀ x, post ⇒ A)) !>).
    { intros σ ?. rewrite simpl_feval_fimpl in H0. rewrite simpl_feval_fimpl. intros.
      simp feval in *. apply H0 in H1 as H2. destruct H2 as []. split... apply H.
      simp feval. split... }

    rewrite fmap_app.

         as_var_ne

        2: {
        injection H4.
        initial_var_of
        Unset Printing Notations.
        rewrite H3 in H4. inversion H4.
        rewrite H7 in H9. inversion H9.

        naive_solver.
        rewrite elem_of_list_pair_indexed in H3.
    remember ((<! pre ∧ $(FForallList (as_var <$> w ++ xs ++ []) <! post ⇒ A !>) !>)) as C.
    set ( initial_var_of <$> w ++ xs) as X.
    set ( (@TVar value) ∘ as_var <$> w ++ xs) as Y.
    (* pose proof (@f_foralllist_one_point _ X Y C). *)
    pose proof (@f_foralllist_one_point M).
    (* subst X. subst Y. *)
    Unset Printing Notations.
    Set Printing Implicit.

    rewrite <- f_foralllist_one_point with (xs:=X) (ts:=Y) (A:=C).
    rewrite <- f_foralllist_one_point.
    intros H A Hfree. simpl.
    assert (<! pre !> ≡ <! pre [_₀\list_to_set (w ++ xs)] !>).
    { unfold subst_initials. admit. }
    rewrite H1. simpl.
    simpl. f_simpl.
    (* intros pre post x t H A Hfree. simpl. *)
    (* assert (<! %pre !> ≡ pre [₀ x \ x]). *)
    (* { rewrite fequiv_subst_non_free... pose proof (final_formula_final pre). *)
    (*   destruct (decide (₀x ∈ formula_fvars pre))... apply H0 in e. simpl in e. discriminate. } *)
    rewrite H0. clear H0.
    rewrite <- simpl_subst_and.
    rewrite <- (f_forall_one_point).
    2:{ simpl. rewrite not_elem_of_singleton. apply initial_var_of_ne. }
    assert
      (<! ⌜₀x = x⌝ ⇒ (pre ∧ (∀ x, post ⇒ A)) !> ⇛
                                <! ⌜₀x = x⌝ ⇒ (post [x \ t] ∧ (∀ x, post ⇒ A)) !>).
    { intros σ ?. rewrite simpl_feval_fimpl in H0. rewrite simpl_feval_fimpl. intros.
      simp feval in *. apply H0 in H1 as H2. destruct H2 as []. split... apply H.
      simp feval. split... }
    rewrite H0. clear H0. rewrite (f_forall_elim t x). rewrite simpl_subst_impl.
    f_simpl. rewrite f_forall_one_point.
    2:{ simpl. rewrite not_elem_of_singleton. apply initial_var_of_ne. }
    rewrite fequiv_subst_non_free.
    2:{ destruct (decide (₀x ∈ formula_fvars <! A [x \ t] !>))... exfalso.
        apply fvars_subst_superset in e. apply elem_of_union in e. destruct e.
        - apply Hfree in H0. simpl in H0. discriminate.
        - pose proof (final_term_final t). apply H1 in H0. simpl in H0. discriminate. }
    reflexivity.
  Qed.

  Lemma r_alternation

  Lemma r_iteration w (I : formula) (v : variable) gcs :
    w : [inv, inv ∧ ¬ (gcomc_any_guard gcs)] ⊑ `PDo gcs`






Lemma assignment : forall pre post x E,
  pre ⇛ post[x \ E] ->
  <{ x : [pre, post] ⊑ x := E }>.
Proof.
  intros pre post w E H A Hfree. simpl. etrans.
  -
  simpl. 
Qed.

Compute wp <{ x : [1 < 2, 2 < 3] }> <[ 5 = 7 ]>.

