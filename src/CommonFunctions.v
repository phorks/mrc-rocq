(* Inductive frel_from_fn (fn : list value -> option value) : list value -> value -> Prop := *)
(*   | FrelFn : forall args fval, fn args = Some fval -> *)
(*     frel_from_fn fn args fval. *)

(* Theorem frel_from_fn_fnal : forall fn, functional_frel (frel_from_fn fn). *)
(* Proof. *)
(*   intros fn args v1 v2 H1 H2. *)
(*   inversion H1; subst. inversion H2; subst. rewrite H0 in H. *)
(*   inversion H. reflexivity. *)
(* Qed. *)

(* Definition fdef_from_fn (n_args : nat) (fn : list value -> option value) := *)
(*   FuncDef 2 (frel_from_fn fn) (frel_from_fn_fnal fn). *)

(* Definition binary_arith_fdef (on_N : nat -> nat -> nat) (on_Z : Z -> Z -> Z) (on_R : R -> R -> R) := *)
(*   fdef_from_fn 2 (fun args => match args with  *)
(*     | [V_Nat n1; V_Nat n2] => @Some value (on_N n1 n2) *)
(*     | [V_Int z1; V_Int z2] => @Some value (on_Z z1 z2) *)
(*     | [V_Nat n1; V_Int z2] => @Some value (on_Z (Z.of_nat n1) z2) *)
(*     | [V_Int z1; V_Nat n2] => @Some value (on_Z z1 (Z.of_nat n2)) *)
(*     | [V_Real r1; V_Real r2] => @Some value (on_R r1 r2) *)
(*     | [V_Nat n1; V_Real r2] => @Some value (on_R (INR n1) r2) *)
(*     | [V_Real r1; V_Nat n2] => @Some value (on_R r1 (INR n2)) *)
(*     | [V_Int z1; V_Real r2] => @Some value (on_R (IZR z1) r2) *)
(*     | [V_Real r1; V_Int z2] => @Some value (on_R r1 (IZR z2))   *)
(*     | _ => None *)
(*     end). *)

(* Definition plus_fdef :=  *)
(*   binary_arith_fdef Nat.add Z.add Rplus. *)

(* Definition minus_fdef :=  *)
(*   binary_arith_fdef Nat.sub Z.sub Rminus. *)

(* Definition mult_fdef := *)
(*   binary_arith_fdef Nat.mul Z.mul Rmult. *)

(* Definition div_fdef := fdef_from_fn 2 (fun args => *)
(*   match args with *)
(*   | [v1; v2] => @Some value (Rdiv (value_to_R v1) (value_to_R v2)) *)
(*   | _ => None *)
(*   end). *)

(* Inductive floor_frel : list value -> value -> Prop := *)
(*   | FloorNat : forall n, floor_frel [V_Nat n] (V_Nat n) *)
(*   | FloorInt : forall z, floor_frel [V_Int z] (V_Int z) *)
(*   | FloorReal : forall r z, (IZR z) <= r < (IZR (z+1)) -> floor_frel [V_Real r] (V_Int z). *)

(* Axiom floor_frel_fnal : functional_frel floor_frel. *)

(* Definition floor_fdef := FuncDef 1 floor_frel floor_frel_fnal. *)

(* Inductive ceiling_frel : list value -> value -> Prop := *)
(*   | CeilingNat : forall n, ceiling_frel [V_Nat n] (V_Nat n) *)
(*   | CeilingInt : forall z, ceiling_frel [V_Int z] (V_Int z) *)
(*   | CeilingReal : forall r z, (IZR z) < r <= (IZR (z+1)) -> ceiling_frel [V_Real r] (V_Int z). *)

(* Axiom ceiling_frel_fnal : functional_frel ceiling_frel. *)

(* Definition ceiling_fdef := FuncDef 1 ceiling_frel ceiling_frel_fnal. *)

(* Inductive int_div_frel : list value -> value -> Prop := *)
(*   | IntDiv : forall v1 v2 v3,  *)
(*     floor_frel [V_Real ((value_to_R v1) / (value_to_R v2))] v3 -> *)
(*     int_div_frel [v1; v2] v3. *)

(* Theorem int_div_frel_fnal : functional_frel int_div_frel. *)
(* Proof. *)
(*   unfold functional_frel. intros args v1 v2 H1 H2. *)
(*   inversion H1; subst. inversion H2; subst. *)
(*   apply (floor_frel_fnal  *)
(*     [V_Real ((value_to_R v0) / (value_to_R v3))] v1 v2); *)
(*     assumption. *)
(* Qed. *)

(* Definition int_div_fdef := FuncDef 2 int_div_frel int_div_frel_fnal. *)

(* Definition default_fctx : fcontext := *)

(* Inductive eq_prel (st : state) (pctx : fcontext) : list term -> bool -> Prop := *)
(*   | EQValue_True : forall t1 v1 t2 v2,  *)
(*     teval st pctx t1 v1 -> *)
(*     teval st pctx t2 v2 -> *)
(*     v1 = v2 -> *)
(*     eq_prel st pctx [T_Const v1; T_Const v2] true *)
(*   | EQValue_False : forall t1 v1 t2 v2,  *)
(*       teval st pctx t1 v1 -> *)
(*       teval st pctx t2 v2 -> *)
(*       v1 <> v2 -> *)
(*       eq_prel st pctx [T_Const v1; T_Const v2] true *)
(*   | EQ_FuncSym : forall f args1 argsv1 args2 argsv2, *)
(*     args_eval st pctx args1 argsv1 -> *)
(*     args_eval st pctx args2 argsv2 -> *)
(*     eq_prel st pctx [(T_Func f args1); (T_Func f args2)] true. *)
