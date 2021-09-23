(* begin hide *)

Require Import Cpdt.CpdtTactics.
Require Export Coq.Strings.String.
(* end hide *)

(*

0.2 From Predicates

Exercise 1. 

Prove these tautologies of propositional logic, using only the tactics apply, assumption, constructor, destruct, intro, intros, left, right, split, and unfold.
(a) (True ∨ False ) ∧ (False ∨ True )
(b) P → ¬ ¬ P
(c) P ∧ (Q ∨ R ) → (P ∧ Q ) ∨ (P ∧ R )
 *)

Lemma taut1 : (True \/ False) /\ (False \/ True).
Proof. split. left. apply I. right. apply I. Qed.

Lemma taut2 : forall (P : Prop), P -> ~ (~ P) .
  intros. unfold not. intros. apply H0. apply H. Qed.

Lemma taut3 : forall (P Q R : Prop), P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
  intros. destruct H. destruct H0. left. split. apply H. apply H0.
  right. split. apply H. apply H0. Qed.

(*
Exercise 2.

Prove the following tautology of first-order logic, using only the tactics apply, assert,
assumption, destruct, eapply, eassumption, and exists. You will probably find the
assert tactic useful for stating and proving an intermediate lemma, enabling a kind
of "forward reasoning", in contrast to the "backward reasoning" that is the default for
Coq tactics. The tactic eassumption is a version of assumption that will do matching
of unification variables. Let some variable T of type Set be the set of individuals. x
is a constant symbol, p is a unary predicate symbol, q is a binary predicate symbol,
and f is a unary function symbol.

p x → (forall x, p x → exists y, q x y ) → (forall x y, q x y → q y (f y )) → exists z, q z (f z )
 *)

Lemma tautol : forall (T : Set) (x : T) (P : T -> Prop) (Q : T -> T -> Prop ) f,
                               P x ->
                               (forall x, P x -> exists y, Q x y) ->
                               (forall x y, Q x y -> Q y (f y)) ->
                               exists z, Q z (f z).
  intros.
  apply H0 in H. destruct H. apply H1 in H. exists x0. assumption. Qed.

(*
Exercise 3. 
Define an inductive predicate capturing when a natural number is an integer multiple
of either 6 or 10. Prove that 13 does not satisfy your predicate, and prove that any
number satisfying the predicate is not odd. It is probably easiest to prove the second
theorem by indicating "odd-ness" as equality to 2 × n + 1 for some n. *)

Inductive six_ten : nat -> Prop :=
| MulNextSix : forall n, six_ten (6 * n)
| MulNextTen : forall n, six_ten (10 * n).
Hint Constructors six_ten.

Lemma six_ten_12 : six_ten 12. assert (H : 12 = 6 * 2). Lia.lia. rewrite H. constructor. Qed. 
Lemma six_ten_0 : six_ten 0. assert (H : 0 = 6 * 0). Lia.lia. rewrite H. constructor. Qed. 

Theorem Thirteen_not : ~(six_ten 13).
  unfold not. intros. 
  inversion H. destruct n; Lia.lia. destruct n; Lia.lia. Qed. 
 
Inductive odd : nat -> Prop :=
| OddN : forall n, odd (2 * n + 1).               
Hint Constructors odd. 

Theorem odd_0_False : odd 0 -> False. 
crush. inversion H; crush. Qed. 

Theorem odd_2n_False : forall n, odd (2 * n)  -> False. 
crush. inversion H; crush. Qed.

Theorem six_ten_not_odd : forall n, six_ten n -> ~(odd n).
  intros. induction H; crush. assert (H' : (n + (n + (n + (n + (n + (n + 0)))))) = 2 * (3 * n)).
  Lia.lia. rewrite H' in H. apply odd_2n_False in H. crush.
  assert (H'' :  (n + (n + (n + (n + (n + (n + (n + (n + (n + (n + 0)))))))))) = 2 * (5 * n)).
  Lia.lia. rewrite H'' in H. apply odd_2n_False in H. crush. Qed.

(* 
Define a simple programming language, its semantics, and its typing rules, and then
prove that well-typed programs cannot go wrong. Specifically:
(a) Define var as a synonym for the natural numbers.
(b) Define an inductive type exp of expressions, containing natural number constants,
natural number addition, pairing of two other expressions, extraction of the first
comp onent of a pair, extraction of the second comp onent of a pair, and variables
(based on the var type you defined).
(c) Define an inductive type cmd of commands, containing expressions and variable
assignments. A variable assignment node should contain the variable being as-
signed, the expression being assigned to it, and the command to run afterward.
(d) Define an inductive type val of values, containing natural number constants and
pairings of values.
(e) Define a type of variable assignments, which assign a value to each variable.
(f ) Define a big-step evaluation relation eval, capturing what it means for an ex-
pression to evaluate to a value under a particular variable assignment. Big step
means that the evaluation of every expression should b e proved with a single in-
stance of the inductive predicate you will define. For instance, 1 + 1 evaluates
to 2 under assignment va  should b e derivable for any assignment va.
(g) Dene a big-step evaluation relation run, capturing what it means for a command
to run to a value under a particular variable assignment. The value of a command
is the result of evaluating its final expression.
(h) Dene a typ e of variable typings, which are like variable assignments, but map
variables to typ es instead of values. You might use p olymorphism to share some
co de with your variable assignments.
(i) Dene typing judgments for expressions, values, and commands. The expression
and command cases will b e in terms of a typing assignment.
(j) Dene a predicate varsType to express when a variable assignment and a variable
typing agree on the typ es of variables.
Prove that any expression that has typ e t under variable typing vt evaluates under
variable assignment va to some value that also has typ e t in vt, as long as va and
vt agree.
(l) Prove that any command that has typ e t under variable typing vt evaluates under
variable assignment va to some value that also has typ e t in vt, as long as va and
vt agree.
A few hints that may b e helpful:
(a) One easy way of defining variable assignments and typings is to define b oth as
instances of a p olymorphic map typ e. The map typ e at parameter T can b e
defined to b e the typ e of arbitrary functions from variables to T. A helpful function
for implementing insertion into such a functional map is eq nat dec, which you
can make available with Require Import Arith.. eq nat dec has a dep endent typ e
that tells you that it makes accurate decisions on whether two natural numb ers
are equal, but you can use it as if it returned a b o olean, e.g., if eq nat dec n m
then E1 else E2.
(b) If you follow the last hint, you may find yourself writing a pro of that involves an
expression with eq nat dec that you would like to simplify. Running destruct
on the particular call to eq nat dec should do the trick. You can automate this
advice with a piece of Ltac:
match goal with
| [ ` context[eq nat dec ?X ?Y ] ] ⇒ destruct (eq nat dec X Y )
end
(c) You probably do not want to use an inductive denition for compatibility of
variable assignments and typings.
(d) The CpdtTactics mo dule from this b o ok contains a variant crush' of crush. crush'
takes two arguments. The first argument is a list of lemmas and other functions
to b e tried automatically in forward reasoning style, where we add new facts
without b eing sure yet that they link into a pro of of the conclusion. The second
argument is a list of predicates on which inversion should b e attempted auto-
matically. For instance, running crush' (lemma1, lemma2 ) pred will search for
chances to apply lemma1 and lemma2 to hyp otheses that are already available,
adding the new concluded fact if suitable hyp otheses can b e found. Inversion will
b e attempted on any hyp othesis using pred, but only those inversions that narrow
the field of possibilities to one p ossible rule will b e kept. The format of the list
arguments to crush' is that you can pass an empty list as tt, a singleton list as the
unadorned single element, and a multiple-element list as a tuple of the elements.
(e) If you want crush' to apply p olymorphic lemmas, you may have to do a little
extra work, if the typ e parameter is not a free variable of your pro of context (so
that crush' do es not know to try it). For instance, if you define a p olymorphic
map insert function assign of some typ e ∀ T : Set, ..., and you want particular applications of assign added automatically with typ e parameter U, you would need
to include assign in the lemma list as assign U (if you have implicit arguments
off ) or assign (T := U ) or @assign U (if you have implicit arguments on).
 *)

Definition var := nat % type. 

(* 
Define an inductive type exp of expressions, containing natural number constants,
natural number addition, pairing of two other expressions, extraction of the first
component of a pair, extraction of the second component of a pair, and variables
(based on the var type you defined).*)
Inductive exp : Set :=
| Var : var -> exp
| Const : nat -> exp
| Plus : nat -> nat -> exp
| Pair : exp -> exp -> exp
| FstP : exp -> exp
| SndP : exp -> exp.
(*
(c) Define an inductive type cmd of commands, containing expressions and variable
assignments. A variable assignment node should contain the variable being assigned, the expression being assigned to it, and the command to run afterward. *)

Inductive cmd : Type :=
| Exp : exp -> cmd
| Assign : var -> exp -> cmd -> cmd.

(*(d) Define an inductive type val of values, containing natural number constants and
pairings of values. *)

Inductive val : Type :=
| NumConst : nat -> val 
| Pairing : val -> val -> val.

(* (e) Define a type of variable assignments, which assign a value to each variable.  *)

Definition total_map (A : Type) := var -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Search nat. 

Definition t_update {A : Type} (m : total_map A)
                    (x : var) (v : A) :=
  fun x' => if PeanoNat.Nat.eqb x x' then v else m x'.

Definition var_map := total_map val.

(* 
(f) Define a big-step evaluation relation eval, capturing what it means for an ex-
pression to evaluate to a value under a particular variable assignment. "Big step"
means that the evaluation of every expression should be proved with a single in-
stance of the inductive predicate you will define. For instance, "1 + 1 evaluates
to 2 under assignment va " should be derivable for any assignment va.
 *)

Inductive eval : exp -> val -> var_map -> Prop :=
| VarEval a va : eval (Var a) (va a) va 
| ConstEval n va : eval (Const n) (NumConst n) va
| PlusEval n1 n2 va : eval (Plus n1 n2) (NumConst (n1 + n2)) va
| PairEval e1 e2 va val1 val2 : eval e1 val1 va -> eval e2 val2 va -> eval (Pair e1 e2) (Pairing val1 val2) va
| FstPEval e v1 v2 va : eval e (Pairing v1 v2) va -> eval (FstP e) v1 va 
| SndPEval e v1 v2 va : eval e (Pairing v1 v2) va -> eval (SndP e) v2 va.

(* 
(g) Define a big-step evaluation relation run, capturing what it means for a command
to run to a value under a particular variable assignment. The value of a command
is the result of evaluating its final expression.
 *)

Inductive run : cmd -> val -> var_map -> Prop :=
| ExpRun e vl va : eval e vl va -> run (Exp e) vl va
| AssignRun e vx va c vl vr : eval e vx va ->
                              run c vl (t_update va vr vx) ->
                              run (Assign vr e c) vl (t_update va vr vx).

(*| AssignRun e vl va vr com cv : eval e vl va ->
                             run com cv (t_update va vr vl) -> run (Assign vr e com) vl va. *)
(* 
(h) Define a type of variable typings, which are like variable assignments, but map
variables to types instead of values. You might use polymorphism to share some
code with your variable assignments.
 *)

Inductive type : Set :=
| TNat : type
| TPair : type -> type -> type.

Definition type_map := total_map type.

(* (i) Define typing judgments for expressions, values, and commands. The expression
and command cases will be in terms of a typing assignment. *)

Fixpoint val_type (v : val) : type :=
  match v with
  | NumConst n => TNat
  | Pairing v1 v2 => TPair (val_type v1) (val_type v2)
  end.                          

Inductive exp_type : exp -> type_map -> type -> Prop :=
  | VarExpT v tm : exp_type (Var v) tm (tm v)
  | ConstExpT n tm : exp_type (Const n) tm TNat
  | PlusExpT n1 n2 tm : exp_type (Plus n1 n2) tm TNat 
  | PairExpT e1 e2 t1 t2 tm : exp_type e1 tm t1 ->
                              exp_type e2 tm t2 ->
                              exp_type (Pair e1 e2) tm (TPair t1 t2)
  | FstPExpT e t1 t2 tm :     exp_type e tm (TPair t1 t2) ->
                              exp_type (FstP e) tm t1                   
  | SndPExpT e t1 t2 tm :     exp_type e tm (TPair t1 t2) ->
                              exp_type (SndP e) tm t2.

Inductive cmd_type : cmd -> type_map -> type -> Prop :=
| ExpT e tm t1 : exp_type e tm t1 -> cmd_type (Exp e) tm t1
| AssignT e tm t vr c t1 : exp_type e tm t ->
                        cmd_type c (t_update tm vr t) t1 ->
                        cmd_type (Assign vr e c) (t_update tm vr t) t1.

(*
(j) Define a predicate varsType to express when a variable assignment and a variable
typing agree on the types of variables
 *)
Definition varsType (vm : var_map) (tm : type_map) :=
  forall x : var, val_type (vm x) = tm x.

(* (k) Prove that any expression that has type t under variable typing vt evaluates under
variable assignment va to some value that also has type t in vt, as long as va and
vt agree. *)
 
Theorem K_case : forall (e : exp) (vt : type_map) (t : type) (va : var_map) (v : val),
         varsType va vt -> exp_type e vt t -> eval e v va -> val_type v = t.
Proof. intros. generalize dependent vt. generalize dependent H1. revert t va v.
       induction e; intros; unfold varsType in H.
       - assert (H' : val_type (va v) = vt v). apply H. (* Var v *)
         assert (H'': va v = v0). inversion H1. auto.
         assert (H''': vt v = t). inversion H0. auto. subst. auto. 
       - inversion H1. inversion H0. crush. (* Const n *)
       - inversion H1. inversion H0. crush. (* Plus n n' *)
       - (* Pair e1 e2 *) inversion H0. subst. inversion H1. subst. crush.
         assert (E : val_type val1 = t1). {
           apply IHe1 with (va:=va) (vt:=vt). auto.
           unfold varsType. apply H. apply H4. }
         assert (E' : val_type val2 = t2). {
           apply IHe2 with (va:=va) (vt:=vt). auto.
           crush. auto. }
         subst. auto.
       -  (* FstP e *)
         inversion H0. subst.
         inversion H1. subst.
         apply IHe with (t:=TPair t t2) (vt:=vt) in H4 .
         inversion H4. auto. auto. auto.
       - (* SndP e*)
         inversion H0. subst.
         inversion H1. subst.
         apply IHe with (t:=TPair t1 t) (vt:=vt) in H4 .
         inversion H4. auto. auto. auto. 
Qed.          

(* 
(l) Prove that any command that has type t under variable typing vt evaluates under
variable assignment va to some value that also has type t in vt, as long as va and
vt agree. *)

Theorem L_case : forall (c : cmd) (vt : type_map) (t : type) (va : var_map) (v : val),
    varsType va vt -> cmd_type c vt t -> run c v va -> val_type v = t.
  Proof. intros. generalize dependent vt. generalize dependent H1. revert t va v.
         induction c; intros.
         - inversion H0. subst. inversion H1. subst. apply K_case with e vt va; crush.
         - inversion H0. inversion H1. crush. eapply IHc in H15. apply H15. eapply H.
           apply H8.
Qed.            

  
