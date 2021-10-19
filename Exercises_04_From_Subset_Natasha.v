Set Implicit Arguments.
Set Asymmetric Patterns.
Require Import Cpdt.CpdtTactics. 
(* Require Export Coq.Strings.String. *)
(* Require Import Bool.  *)

(*
All of the notations defined in this chapter, plus some extras, are available for import from
the module MoreSpecif of the book source. *)

Print sumbool. 
Notation "!" := (False_rec _ _) : specif_scope.
Notation "[ e ]" := (exist _ e _) : specif_scope.
Notation "x <== e1 ; e2" := (let (x, _) := e1 in e2)
(right associativity, at level 60) : specif_scope.
Local Open Scope specif_scope.
Delimit Scope specif_scope with specif.

Notation "'Yes'" := (left _ _) : specif_scope.
Notation "'No'" := (right _ _) : specif_scope.
Notation "'Reduce' x" := (if x then Yes else No) (at level 50) : specif_scope.

Notation "x || y" := (if x then Yes else Reduce y) (at level 50, left associativity) : specif_scope.
(* 1. Write a function of type ∀ n m : nat , { n ≤ m } + { n > m }. That is, this function
decides whether one natural is less than another, and its dependent type guarantees
that its results are accurate.
*)
Definition one_less_than_another : forall n m : nat, { n <= m } + { n > m }.
 refine (fix f (n m : nat) : {n <= m} + {n > m} :=
 match n, m with
 | O, _ => Yes
 | _, O => No              
 | S n', S m' => Reduce (f n' m')
 end); crush. 
Defined.

Eval compute in one_less_than_another 2 2.
Eval compute in one_less_than_another 3 2.
     
(* 2.
(a) Define var , a type of propositional variables, as a synonym for nat . *)

Definition var := nat. 

(* (b) Define an inductive type prop of propositional logic formulas, consisting of vari-
ables, negation, and binary conjunction and disjunction. *)

Inductive prop : Set :=
| Var : var -> prop
| Neg : prop -> prop
| Conj : prop -> prop -> prop 
| Disj : prop -> prop -> prop.

(*
(c) Define a function propDenote from variable truth assignments and props to Prop ,
based on the usual meanings of the connectives. Represent truth assignments as
    functions from var to bool. *)
Fixpoint propDenote (tr : var -> bool) (p : prop) : Prop :=
  match p with
  | Var vr => if tr vr then True else False 
  | Neg p => ~(propDenote tr p)
  | Conj p1 p2 => (propDenote tr p1) /\ (propDenote tr p2)
  | Disj p1 p2 => (propDenote tr p1) \/ (propDenote tr p2)    
  end.

(* 
(d) Define a function bool_true_dec that checks whether a boolean is true, with a
maximally expressive dependent type. That is, the function should have type ∀
b , { b = true } + { b = true → False }. *)

Definition bool_true_dec : forall (b : bool), {b = true} + {b = true -> False}.
  refine (fun b =>
            match b with
            | true => Yes
            | false => No
            end). crush. crush. 
Defined.

(* (e) Define a function decide that determines whether a particular prop is true under
a particular truth assignment. That is, the function should have type ∀ ( truth
: var → bool ) ( p : prop ), { propDenote truth p } + {~ propDenote truth p }.
This function is probably easiest to write in the usual tactical style, instead of
programming with refine . The function bool true dec may come in handy as a
hint. *)

Definition decide : forall (truth : var -> bool) (p : prop),
    {propDenote truth p} + {~ propDenote truth p}.
intros. induction p; crush. destruct (truth v); crush. 
Defined.

(* (f) Define a function negate that returns a simplified version of the negation of a
prop . That is, the function should have type ∀ p : prop , { p' : prop | ∀ truth ,
propDenote truth p ↔ ¬ propDenote truth p' }. To simplify a variable, just
negate it. Simplify a negation by returning its argument. Simplify conjunctions
and disjunctions using De Morgan's laws, negating the arguments recursively and
switching the kind of connective. Your decide function may be useful in some
of the proof obligations, even if you do not use it in the computational part of
negate 's definition. Lemmas like decide allow us to compensate for the lack of a
                             general Law of the Excluded Middle in CIC. *)

Definition negate : forall (p : prop), {p' : prop | forall truth, propDenote truth p <->
                                       ~ (propDenote truth p')}.
  refine (fix f (p : prop) : {p' : prop | forall truth, propDenote truth p <->
                                       ~ (propDenote truth p')} := 
            match p with
            | Var vr => [ (Neg (Var vr)) ]
            | Neg p => [ p ]
            | Conj p1 p2 => p1' <== f p1;
                            p2' <== f p2;
                            [ Disj p1' p2' ]
            | Disj p1 p2 => p1' <== f p1;
                            p2' <== f p2;
                            [ Conj p1' p2' ]
            end); crush.
  destruct (truth vr); crush. 
  apply i with truth; crush.
  apply i0 with truth; crush.
  apply i with truth; crush.
  apply i0 with truth; crush.
  destruct (decide truth p1'); crush. 
Defined. 
  
(* 3. Implement the DPLL satisfiability decision procedure for boolean formulas in conjunc-
tive normal form, with a dependent type that guarantees its correctness. An example
of a reasonable type for this function would be ∀ f : formula , { truth : tvals | formu-
laTrue truth f } + { ∀ truth , ¬ formulaTrue truth f }. Implement at least "the basic
backtracking algorithm" as defined here:

                             http://en.wikipedia.org/wiki/DPLL_algorithm

It might also be instructive to implement the unit propagation and pure literal elimi-
nation optimizations described there or some other optimizations that have been used
in modern SAT solvers. *)

Definition sat : forall f : formula, { truth : tvals | formulaTrue truth f } + { forall truth , ~ formulaTrue truth f }
                                                                         

