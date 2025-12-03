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

Open Scope stdpp_scope.
Open Scope refiney_scope.


Section prog.
  Context {M : model}.
  Local Notation term := (term (value M)).
  Local Notation final_term := (final_term (value M)).
  Local Notation formula := (formula (value M)).
  Local Notation final_formula := (final_formula (value M)).

  Inductive prog : Type :=
  | PAsgn (xs : list final_variable) (ts: list final_term) `{OfSameLength _ _ xs ts}
  | PSeq (p1 p2 : prog)
  | PIf (gcmds : list (final_formula * prog))
  | PSpec (w : list final_variable) (pre : final_formula) (post : formula)
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

  Global Instance pequiv : Equiv prog := λ p1 p2, p1 ⊑ p2 ∧ p2 ⊑ p1.
  Global Instance refines_refl : Reflexive refines.
  Proof with auto. intros ? ?.  reflexivity. Qed.

  Global Instance refines_trans : Transitive refines.
  Proof with auto. intros ? ? ? ? ? ?... transitivity (wp y A); naive_solver. Qed.

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
    asgn_args_open_vars : list final_variable;
    asgn_xs : list final_variable;
    asgn_ts : list final_term;
    asgn_of_same_length : OfSameLength asgn_xs asgn_ts;
  }.

  (* Local Definition split_asgn_list (lhs : list final_variable) (rhs : list asgn_rhs_term) *)
  (*   `{H : OfSameLength _ _ lhs rhs} : asgn_args. *)
  (* Proof. *)

  Definition split_asgn_list (lhs : list final_variable) (rhs : list asgn_rhs_term)
    `{H : OfSameLength _ _ lhs rhs} : asgn_args :=
    of_same_length_rect
      id
        (λ rec x t args,
          let (opens, xs, ts, _) := (rec args : asgn_args) in
          match t with
          | OpenRhsTerm => (mkAsgnArgs (opens ++ [x]) xs ts _)
          | FinalRhsTerm t => (mkAsgnArgs opens (x::xs) (t::ts) _)
          end)
        (mkAsgnArgs [] [] [] _)
        lhs rhs.

  Lemma split_asgn_list_no_opens xs ts `{OfSameLength _ _ xs ts} :
    split_asgn_list xs (FinalRhsTerm <$> ts) = mkAsgnArgs [] xs ts _.
  Proof.
    generalize dependent ts. induction xs as [|x xs IH]; simpl; intros.
    - assert (H':=H). apply of_same_length_nil_inv_l in H' as ->. simpl...
      unfold split_asgn_list. simpl. f_equal. apply OfSameLength_pi.
    - assert (H':=H). apply of_same_length_cons_inv_l in H' as (t&ts'&->&?).
      rename ts' into ts. unfold split_asgn_list in IH. simpl.
      unfold split_asgn_list. simpl.
      apply of_same_length_rest in H as H'.
      (* PI shenanigans *)
      assert ((@of_same_length_rest final_variable asgn_rhs_term x xs (FinalRhsTerm t)
                 (list_fmap final_term asgn_rhs_term FinalRhsTerm ts)
                 (@of_same_length_fmap_r final_variable final_term asgn_rhs_term
                    (x :: xs) (t :: ts) FinalRhsTerm H)) =
                (@of_same_length_fmap_r final_variable final_term asgn_rhs_term xs
                   ts FinalRhsTerm H') ) as ->.
      { apply OfSameLength_pi. }
      rewrite IH. f_equiv. apply OfSameLength_pi.
  Qed.

  Definition PAsgnWithOpens (lhs : list final_variable) (rhs : list asgn_rhs_term)
                            `{OfSameLength _ _ lhs rhs} : prog :=
    let (opens, xs, ts, _) := split_asgn_list lhs rhs in
    PVarList (as_var <$> remove_dups opens) (PAsgn xs ts).

  Lemma PAsgnWithOpens_no_opens xs ts `{OfSameLength _ _ xs ts} :
    PAsgnWithOpens xs (FinalRhsTerm <$> ts) = PAsgn xs ts.
  Proof.
    unfold PAsgnWithOpens. rewrite split_asgn_list_no_opens. simpl. reflexivity.
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
    (in custom prog at level 95 ) : refiney_scope.

Notation "'|[' 'con' x '⦁' y ']|' " :=
  (PConst x y)
    (in custom prog at level 95, no associativity,
        x constr at level 0, y custom prog at next level) : refiney_scope.

Notation "'|[' 'con*' xs '⦁' y ']|' " :=
  (PConstList xs y)
    (in custom prog at level 95 ) : refiney_scope.

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
  Local Notation term := (term value).
  Local Notation formula := (formula value).
  Local Notation final_term := (final_term value).

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w : list final_variable.
  Implicit Types xs : list final_variable.

  Lemma wp_asgn xs ts A `{OfSameLength _ _ xs ts} :
    wp <{ *xs := *$(FinalRhsTerm <$> ts) }> A ≡ <! A[[ ↑ₓ xs \ ⇑ₜ ts]] !>.
  Proof with auto.
    rewrite PAsgnWithOpens_no_opens. simpl...
  Qed.

End prog.
