From stdpp Require Import base.

Inductive value_ty :=
| TNat.


Inductive type :=
| TTerm : value_ty → type
| TProg : type
| TProp : type.

Inductive expr' (var : type → Type) : type → Type :=
  | EVar : ∀ t, var t → expr' var t
  | ENot : expr' var TProp → expr' var TProp
  | EAnd : expr' var TProp → expr' var TProp → expr' var TProp
  | EExists : ∀ ty, (var ty → expr' var TProp) → expr' var TProp
.

Definition expr ty := ∀ var, expr' var ty.

Inductive expr (var : type -> Type) : type -> Type :=
| Var    : forall t, var t -> expr var t
| App    : forall t1 t2, expr var (Arr t1 t2) -> expr var t1 -> expr var t2
| Abs    : forall t1 t2, (var t1 -> expr var t2) -> expr var (Arr t1 t2)
| Forall : forall t, (var t -> expr var PropT) -> expr var PropT
| Exists : forall t, (var t -> expr var PropT) -> expr var PropT
| And    : expr var PropT -> expr var PropT -> expr var PropT
| PApp   : forall p, hlist (expr var) (map Base (pred_ar Sg p)) -> expr var PropT
| FApp   : forall f, hlist (expr var) (map Base (fst (func_ar Sg f)))
                    -> expr var (Base (snd (func_ar Sg f)))
                    -> expr var PropT
end.
