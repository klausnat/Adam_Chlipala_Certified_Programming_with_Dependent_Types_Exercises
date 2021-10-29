(* begin hide *)
Set Implicit Arguments.
Set Asymmetric Patterns.
Require Import Cpdt.CpdtTactics.
Require Import List. 
(* end hide *)

(* we need section hlist here. with all it's functions and types: *)
Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  Definition hhd ls (hl : hlist ls) :=
    match hl in hlist ls return match ls with
                                  | nil => unit
                                  | x :: _ => B x
                                end with
      | HNil => tt
      | HCons _ _ v _ => v
    end.

  Definition htl ls (hl : hlist ls) :=
    match hl in hlist ls return match ls with
                                  | nil => unit
                                  | _ :: ls' => hlist ls'
                                end with
      | HNil => tt
      | HCons _ _ _ hl' => hl'
    end.

  Variable elm : A.

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  Fixpoint hget ls (mls : hlist ls) : member ls -> B elm :=
    match mls with
      | HNil => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => B elm
                                          | _ :: _ => unit
                                        end) with
          | HFirst _ => tt
          | HNext _ _ _ => tt
        end
      | HCons _ _ x mls' => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => Empty_set
                                          | x' :: ls'' =>
                                            B x' -> (member ls'' -> B elm) -> B elm
                                        end) with
          | HFirst _ => fun x _ => x
          | HNext _ _ mem' => fun _ get_mls' => get_mls' mem'
        end x (hget mls')
    end.

  Fixpoint happ (ls1 : list A) (hl1 : hlist ls1) : forall ls2, hlist ls2 -> hlist (ls1 ++ ls2) :=
    match hl1 in hlist ls1 return forall ls2, hlist ls2 -> hlist (ls1 ++ ls2) with
      | HNil => fun _ hl2 => hl2
      | HCons _ _ x hl1' => fun _ hl2 => HCons x (happ hl1' hl2)
    end.

  Variable f : forall x, B x.

  Fixpoint hmake (ls : list A) : hlist ls :=
    match ls with
      | nil => HNil
      | x :: ls' => HCons (f x) (hmake ls')
    end.

  Theorem hget_hmake : forall ls (m : member ls),
    hget (hmake ls) m = f elm.
    induction ls; crush;
      match goal with
        | [ |- context[match ?E with HFirst _ => _ | HNext _ _ _ => _ end] ] => dep_destruct E
      end; crush.
  Qed.
End hlist.

(*
1. Implement and prove correct a substitution function for simply typed lambda calculus.
  In particular: *)
  
(*  (a) Define a datatype type of lambda types, including just booleans and function
    types.  *)

Inductive type : Set :=
| Bool : type
| Func : type -> type -> type.

(* (b) Define a type family exp : list type → type → Type of lambda expressions,
including boolean constants, variables, and function application and abstraction. *)

(* exp ts t , is an expression that has type t and whose free vars have types in the list ts  *)
Inductive exp : list type -> type -> Type :=
| Const : forall ts, exp ts Bool
| Var : forall ts t, member t ts -> exp ts t
| App : forall ts dom ran, exp ts (Func dom ran) -> exp ts dom -> exp ts ran
| Abs : forall ts dom ran, exp (dom :: ts) ran -> exp (ts) (Func dom ran).

Arguments Const {ts}.

(* (c) Implement a definitional interpreter for exps, by way of a recursive function over
expressions and substitutions for free variables, like in the related example from
the last chapter. *)

Fixpoint typeDenote (t : type) : Set :=
  match t with
  | Bool => bool
  | Func t1 t2 => typeDenote t1 -> typeDenote t2
  end.                                             

Fixpoint expDenote ts t (e : exp ts t) : hlist typeDenote ts -> typeDenote t :=
  match e with
  | Const _ => fun x => match x with
                        | (HCons _ _ a _) => a
                        | _ => x                       
                        end
  | Var _ _  mem => fun s => hget s mem 
  | App _ _ _ e1 e2 => fun s => (expDenote e1 s) (expDenote e2 s)
  | Abs _ _ _ e' => fun s => fun x => expDenote e' (HCons x s)
  end. 
