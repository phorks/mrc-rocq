From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Strings.String.
From stdpp Require Import base gmap.
From MRC Require Import Prelude.
From MRC Require Import SeqNotation.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.

Open Scope stdpp_scope.
Open Scope refiney_scope.

Definition subst_initials {M} A (w : gset final_variable) : (formula (value M)) :=
  simult_subst A (set_to_map (λ x, (₀x, (TVar x))) w).

Notation "A [_₀\ w ]" := (subst_initials A w)
                            (in custom formula at level 74, left associativity,
                                A custom formula,
                                w constr at level 200) : refiney_scope.

Section prog.
  Context {M : model}.
  Local Notation term := (term (value M)).
  Local Notation final_term := (final_term (value M)).
  Local Notation formula := (formula (value M)).
  Local Notation final_formula := (final_formula (value M)).

  Local Notation asgn_map := (gmap final_variable final_term).

  Inductive prog : Type :=
  | PAsgn (m : asgn_map)
  | PSeq (p1 p2 : prog)
  | PIf (gcmds : list (formula * prog))
  | PSpec (w : gset final_variable) (pre : final_formula) (post : formula)
  | PVar (x : variable) (p : prog)
  | PConst (x : variable) (p : prog).

  Fixpoint PVarList (xs : list variable) (p : prog) :=
    match xs with
    | [] => p
    | x :: xs => PVar x (PVarList xs p)
    end.

  Fixpoint PConstList (xs : list variable) (p : prog) :=
    match xs with
    | [] => p
    | x :: xs => PConst x (PConstList xs p)
    end.


  Notation gcmd_list := (list (formula * prog)).
  Definition gcmd_comprehension (gs : list formula) (f : formula → prog) : gcmd_list :=
    map (λ A, (A, f A)) gs.

  Fixpoint modified_final_vars p : gset final_variable :=
    match p with
    | PAsgn m => dom m
    | PSeq p1 p2 => modified_final_vars p1 ∪ modified_final_vars p2
    | PIf gcmds => ⋃ ((modified_final_vars ∘ snd) <$> gcmds)
    | PSpec w pre post => w
    | PVar x p => modified_final_vars p
    | PConst x p => modified_final_vars p
    end.

  (* TODO: move it near to as_var_F *)
  Definition as_var_set (vs : gset final_variable) : gset variable :=
    set_map as_var vs.

  Definition asgn_map_to_vt_map (m : asgn_map) : gmap variable term :=
    list_to_map (prod_map as_var as_term <$> map_to_list m).

  Definition modified_vars p : gset variable := as_var_set (modified_final_vars p).
  Notation "'Δ' p" := (modified_vars p) (at level 50).

  Fixpoint prog_fvars p : gset variable :=
    match p with
    | PAsgn m => as_var_set (dom m)
    | PSeq p1 p2 => prog_fvars p1 ∪ prog_fvars p2
    | PIf gcmds => ⋃ ((prog_fvars ∘ snd) <$> gcmds)
    | PSpec w pre post => as_var_set w ∪ formula_fvars pre ∪ formula_fvars post
    | PVar x p => prog_fvars p ∖ {[x]}
    | PConst x p => prog_fvars p ∖ {[x]}
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
    | PAsgn m => simult_subst A (asgn_map_to_vt_map m)
    | PSeq p1 p2 => wp p1 (wp p2 A)
    | PIf gcs => <! $(any_guard gcs) ∧ $(all_cmds gcs A) !>
    | PSpec w pre post =>
        <! pre ∧ (∀* $(set_to_list (as_var_set w)), post ⇒ A)[_₀\ w] !>
    | PVar x p => <! ∀ x, $(wp p A) !>
    | PConst x p => <! ∃ x, $(wp p A) !>
    end.

  (* ******************************************************************* *)
  (* definition and properties of ⊑ and ≡ on progs                       *)
  (* ******************************************************************* *)
  Global Instance refines : SqSubsetEq prog := λ p1 p2,
    ∀ A : final_formula,
      (∀ x, x ∈ formula_fvars A → var_is_initial x = false) ->
      wp p1 A ⇛ (wp p2 A).

  Global Instance pequiv : Equiv prog := λ p1 p2, p1 ⊑ p2 ∧ p2 ⊑ p1.
  Global Instance refines_refl : Reflexive refines.
  Proof with auto. intros ? ? ?. reflexivity. Qed.

  Global Instance refines_trans : Transitive refines.
  Proof with auto. intros ? ? ? ? ? ? ?... transitivity (wp y A); naive_solver. Qed.

  Global Instance pequiv_refl : Reflexive pequiv.
  Proof with auto. split; reflexivity. Qed.

  Global Instance pequiv_sym : Symmetric pequiv.
  Proof with auto. intros p1 p2. unfold pequiv. naive_solver. Qed.

  Global Instance pequiv_trans : Transitive pequiv.
  Proof with auto.
    intros p1 p2 p3 [H12 H21] [H23 H32]. split.
    - transitivity p2...
    - transitivity p2...
  Qed.

  Global Instance pequiv_equiv : Equivalence pequiv.
  Proof.
    split.
    - exact pequiv_refl.
    - exact pequiv_sym.
    - exact pequiv_trans.
  Qed.

  Global Instance refines_antisym : Antisymmetric prog pequiv refines.
  Proof. intros p1 p2 H12 H21. split; assumption. Qed.

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

  Axiom rec_ind : ∀ F P, F P ≡ P → PRec F ⊑ P.

  (* while g => p    =    re P ⦁ if g then p; P fi er *)
  Definition PWhile (gcmds : gcmd_list) :=
    PRec (λ P, PIf gcmds).


  (* ******************************************************************* *)
  (* some extreme programs                                               *)
  (* ******************************************************************* *)

  Definition abort := PSpec ∅ <!! false !!> <! true !>.
  Definition abort_w w := PSpec w <!! false !!> <! true !>.
  Definition choose_w w := PSpec w <!! true !!> <! true !>.
  Definition skip := PSpec ∅ <!! true !!> <! true !>.
  Definition magic := PSpec ∅ <!! true !!> <! false !>.
  Definition magic_w w := PSpec w <!! true !!> <! false !>.

  (* ******************************************************************* *)
  (* open assignment                                                     *)
  (* ******************************************************************* *)
  Variant asgn_rhs_term :=
    | OpenRhsTerm
    | FinalRhsTerm (t : final_term).

  Record asgn_args := mkAsgnArgs {
    asgn_args_open_vars : list final_variable;
    asgn_args_map  : asgn_map
  }.

  (* TODO: move it *)
  Definition of_same_length_rest {A B} {x1 : A} {l1 : list A} {x2 : B} {l2 : list B}
                               (H :OfSameLength (x1::l1) (x2::l2)) : OfSameLength l1 l2.
  Proof. unfold OfSameLength in *. simpl in H. lia. Qed.

  Local Definition split_asgn_list (lhs : list final_variable) (rhs : list asgn_rhs_term)
    `{H : OfSameLength _ _ lhs rhs} : asgn_args.
  Proof.
    generalize dependent rhs.
    induction lhs as [|x lhs']; destruct rhs as [|t rhs']; intros.
    - exact (mkAsgnArgs [] ∅).
    - exact (mkAsgnArgs [] ∅). (* doesn't happen because of OfSameLength *)
    - exact (mkAsgnArgs [] ∅). (* doesn't happen because of OfSameLength *)
    - apply of_same_length_rest in H. apply IHlhs' in H as [opens map].
      destruct t.
      + exact (mkAsgnArgs (opens ++ [x]) map).
      + exact (mkAsgnArgs opens (<[x:=t]> map)).
  Defined.

  Definition PAsgnWithOpens (lhs : list final_variable) (rhs : list asgn_rhs_term)
                            `{OfSameLength _ _ lhs rhs} : prog :=
    let (opens, map) := split_asgn_list lhs rhs in
    PVarList (as_var <$> remove_dups opens) (PAsgn map).

End prog.

Declare Custom Entry term_seq_notation.
Declare Custom Entry term_seq_elem.

Notation "xs" := (xs) (in custom term_seq_notation at level 0,
                       xs custom term_seq_elem)
    : refiney_scope.
Notation "∅" := ([]) (in custom term_seq_notation at level 0)
    : refiney_scope.

Notation "x" := ([FinalRhsTerm (as_final_term x)]) (in custom term_seq_elem at level 0, x custom term at level 200)
    : refiney_scope.
Notation "?" := ([OpenRhsTerm]) (in custom term_seq_elem at level 0) : refiney_scope.
Notation "* x" := x (in custom term_seq_elem at level 0, x constr at level 0)
    : refiney_scope.
Notation "*$( x )" := x (in custom term_seq_elem at level 5, x constr at level 200)
    : refiney_scope.
Notation "x , .. , y" := (app x .. (app y []) ..)
                           (in custom term_seq_elem at level 10,
                               x custom term_seq_elem at next level,
                               y custom term_seq_elem at next level) : refiney_scope.

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
                           xs custom seq_notation at level 94,
                           ts custom term_seq_notation at level 94,
                           no associativity)
    : refiney_scope.

Notation "p ; q" := (PSeq p q)
                      (in custom prog at level 120, right associativity)
    : refiney_scope.

Notation "A → p" := ((A, p)) (in custom gcmd at level 60,
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
  (PSpec (list_to_set w) p q)
    (in custom prog at level 95, no associativity,
        w custom seq_notation at level 94,
        p custom formula at level 85, q custom formula at level 85)
    : refiney_scope.

Notation ": [ p , q ]" :=
  (PSpec ∅ p q)
    (in custom prog at level 95, no associativity,
        p custom formula at level 85, q custom formula at level 85)
    : refiney_scope.

Axiom M : model.
Axiom p1 p2 : @prog M.
Axiom pre : @final_formula (value M).
Axiom post : @formula (value M).
Axiom x y z : final_variable.
Axiom xs ys : list final_variable.
Definition pp := <{ $p1 ; $p2 }>.
Definition pp2 := <{ ∅ : [<! pre !>, post] }>.
Definition pp3 := <{ x, y, z := y, x, ? }> : @prog M.

Notation "'|[' 'var' x '⦁' y ']|' " :=
  (PVar x y)
    (in custom prog at level 95, no associativity,
        x constr at level 0, y custom prog) : refiney_scope.

Notation "'|[' 'var*' xs '⦁' y ']|' " :=
  (PVarList xs y)
    (in custom prog at level 95 ) : refiney_scope.

Notation "'|[' 'con' x '⦁' y ']|' " :=
  (PConst x y)
    (in custom prog at level 95, no associativity,
        x constr at level 0, y custom prog at next level) : refiney_scope.

Notation "'|[' 'con*' xs '⦁' y ']|' " :=
  (PVarList xs y)
    (in custom prog at level 95 ) : refiney_scope.
