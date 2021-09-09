(* begin hide *)
Require Import List.

Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.
Require Import Cpdt.CpdtTactics.
Require Import String.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)

(*  O.1 FROM INDUCTIVE TYPES *)
(* Exercise 1. Define an inductive type truth with three constructors, Yes, No, and Maybe. Yes
stands for certain truth, No for certain falsehood, and Maybe for an unknown situation.
Define "not","and",and "or" for this replacement boolean algebra. Prove that your
implementation of "and" is commutative and distributes over your implementation of
"or".
*)
Inductive truth : Set :=
| Yes : truth
| No : truth 
| Maybe : truth.

Definition Not c : truth :=
  match c with
  | Yes => No 
  | No => Yes
  | Maybe => Maybe
  end.              

Definition And a b : truth :=
  match a with
  | Yes => match b with
           | Yes => Yes
           | _ => No
           end             
  | No => No
  | Maybe => No
  end.

Definition Or a b : truth :=
  match a with
  | Yes => Yes
  | No => match b with
           | Yes => Yes
           | No => No 
           | Maybe => Maybe
           end             
  | Maybe => match b with
             | Yes => Yes
             | No => Maybe 
             | Maybe => Maybe
             end             
  end.

(* Prove that "And" is commutative and distributes over implementation of "Or" *)

Lemma And_commutative : forall a b, And a b = Yes -> And b a = Yes.
  intros. destruct a eqn:E; inversion H; crush. Qed.

Lemma And_commut : forall a b, And a b = And b a.
intros. destruct a eqn:E; destruct b eqn:G; crush. Qed. 
  
Lemma And_distributes_over_Or : forall a b c, And a (Or b c) = Yes ->
                                              Or (And a b) (And a c) = Yes.
  intros. destruct a; destruct b; destruct c; inversion H; crush. Qed.

Lemma And_distributes_over_Or' : forall a b c, And a (Or b c) = Or (And a b) (And a c).
intros. destruct a; destruct b; destruct c; crush. Qed. 

(* Exercise 2.
Define an inductive typ e slist that implements lists with supp ort for constant-time
concatenation. This typ e should b e p olymorphic in a choice of typ e for data values in
lists. The typ e slist should have three constructors, for empty lists, singleton lists, and
concatenation. Define a function atten that converts slist s to list s. (You will want
to run Require Import List. to bring list definitions into scop e.) Finally, prove that
atten distributes over concatenation, where the two sides of your quantified equality
will use the slist and list versions of concatenation, as appropriate. Recall from Chapter
2 that the infix op erator ++ is syntactic sugar for the list concatenation function app. *)

(* lists for constant-tyme concatenation *)

Inductive slist ( A : Set ) : Set :=
  | Sl_Nil : slist A
  | Sl_Single (x : A) : slist A 
  | Sl_Concat : slist A -> slist A -> slist A.      

Fixpoint flatten (A : Set) (ls : slist A) : list A :=
  match ls with
  | Sl_Nil => nil
  | Sl_Single x => x :: nil
  | Sl_Concat xs ys => (flatten xs) ++ (flatten ys)
  end.                                   

Lemma flatten_Distrs_Over_Concat : forall A (xs ys : slist A),
    flatten (Sl_Concat xs ys) = flatten xs ++ flatten ys.
  intros. induction xs; crush. Qed. 

(* Exercise 3 : Mo dify the first example language of Chapter 2 to include variables, where variables are
represented with nat. Extend the syntax and semantics of expressions to accommo date
the change. Your new expDenote function should take as a new extra first argument
a value of typ e var → nat, where var is a synonym for naturals-as-variables, and the
function assigns a value to each variable. Define a constant folding function which do es
a b ottom-up pass over an expression, at each stage replacing every binary op eration
on constants with an equivalent constant. Prove that constant folding preserves the
meanings of expressions. *)

Inductive binop : Set := Plus | Times.
Definition var := nat. 

Inductive exp : Set :=
| Var : var -> exp
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote := fun b =>
  match b with
  | Plus => plus
  | Times => mult
  end.

Fixpoint expDenote (fn : var -> nat) (e : exp) : nat :=
  match e with
  | Var str => fn str
  | Const n => n
  | Binop b e1 e2 => (binopDenote b) (expDenote fn e1) (expDenote fn e2)
  end.

 Eval simpl in expDenote id (Const 4).
 Eval compute in expDenote id (Var 5).

 (* at each stage replacing every binary op eration on constants with an equivalent constant *)
 Fixpoint constantFolding (e : exp) : exp :=
  match e with
  | Binop b e1 e2 => match (constantFolding e1), (constantFolding e2) with
                     | Const n1, Const n2 => Const ((binopDenote b) n1 n2)
                     | e11, e22 => Binop b e11 e22
                     end
  | _ => e                     
  end.

 
 Theorem cFpreserves : forall (e : exp) vars, expDenote vars (constantFolding e) = expDenote vars e.
 Proof. intros. induction e; crush. destruct (constantFolding e1); crush. destruct (constantFolding e2); crush. Qed. 

 (* Exercise 4 : 
Reimplement the second example language of Chapter 2 to use mutually inductive
typ es instead of dep endent typ es. That is, define two separate (non-dep endent) induc-
tive typ es nat exp and bool exp for expressions of the two different typ es, rather than
a single indexed typ e. To keep things simple, you may consider only the binary op era-
tors that take naturals as op erands. Add natural numb er variables to the language, as
in the last exercise, and add an if expression form taking as arguments one b o olean
expression and two natural numb er expressions. Define semantics and constant-folding
functions for this new language. Your constant folding should simplify not just binary
op erations (returning naturals or b o oleans) with known arguments, but also "if"  ex-
pressions with known values for their test expressions but p ossibly undetermined "then"
and "else" cases. Prove that constant-folding a natural numb er expression preserves its
meaning.
 *)

 (* a mutually inductive types *)
 
Inductive binopNat : Set := PlusNat | TimesNat.

Inductive binopBool : Set := LebBool | EqBool.
Definition binopNatDenote := fun binop =>
                               match binop with
                               | PlusNat => plus
                               | TimesNat => mult
                               end.                    
Definition binopBoolDenote := fun binop =>
                               match binop with
                               | LebBool => leb
                               | EqBool => beq_nat
                               end.                    

Inductive nat_exp : Set :=
 | VarNat : var -> nat_exp
 | ConstNat : nat -> nat_exp
 | BinopNat : binopNat -> nat_exp -> nat_exp -> nat_exp
 | If : bool_exp -> nat_exp -> nat_exp -> nat_exp
with bool_exp : Set :=
| ConstBool : bool -> bool_exp
| BinopBool : binopBool -> nat_exp -> nat_exp -> bool_exp.                        
(* let's define semantics *)
Fixpoint expDenote_mutual_nat (fn : var -> nat) (e : nat_exp) : nat :=
  match e with
  | VarNat str => fn str
  | ConstNat n => n
  | BinopNat b e1 e2 => (binopNatDenote b) (expDenote_mutual_nat fn e1) (expDenote_mutual_nat fn e2)
  | If be e1 e2 => if (expDenote_mutual_bool fn be)
                   then (expDenote_mutual_nat fn e1)
                   else (expDenote_mutual_nat fn e2) 
  end
with expDenote_mutual_bool (fn : var -> nat) (b : bool_exp) : bool :=
  match b with
  | ConstBool b => b 
  | BinopBool bp e1 e2 => (binopBoolDenote bp) (expDenote_mutual_nat fn e1) (expDenote_mutual_nat fn e2)
  end.       
 (* and constant folding functions *)

Fixpoint constantFolding_mut_nat (e : nat_exp) : nat_exp :=
  match e with
  | BinopNat b e1 e2 => match constantFolding_mut_nat e1, constantFolding_mut_nat e2 with
                        | ConstNat n1, ConstNat n2 => ConstNat ((binopNatDenote b) n1 n2)  
                        | e11, e22 => BinopNat b e11 e22
                        end
  | If be e1 e2 => match constantFolding_mut_bool be with
                   | ConstBool b => if b then constantFolding_mut_nat e1 else constantFolding_mut_nat e2
                   | be' => If be' (constantFolding_mut_nat e1) (constantFolding_mut_nat e2)
                   end            
  | _ => e                    
  end                    
  with constantFolding_mut_bool (b : bool_exp) : bool_exp :=
         match b with
         | BinopBool bp e1 e2 => match (constantFolding_mut_nat e1), (constantFolding_mut_nat e2) with
                                 | ConstNat ee1, ConstNat ee2 => ConstBool (binopBoolDenote bp ee1 ee2)
                                 | ee1, ee2 => BinopBool bp ee1 ee2
                                 end                                      
         | _ => b

  end.

Scheme nat_exp_mut := Induction for nat_exp Sort Prop
with bool_exp_mut := Induction for bool_exp Sort Prop.

Check nat_exp_ind.
Check nat_exp_mut.

Theorem cFpreserves_mut : forall (e : nat_exp) vars,
    expDenote_mutual_nat vars (constantFolding_mut_nat e) = expDenote_mutual_nat vars e.
Proof.
  intros.
  revert e.
  
  apply (nat_exp_mut
       (fun e : nat_exp => expDenote_mutual_nat vars (constantFolding_mut_nat e) = expDenote_mutual_nat vars e)
       (fun b : bool_exp => expDenote_mutual_bool vars (constantFolding_mut_bool b) = expDenote_mutual_bool vars b )); crush.
  destruct (constantFolding_mut_nat n); crush.
  destruct (constantFolding_mut_nat n0); crush.
  destruct (constantFolding_mut_bool b); crush.
  destruct (expDenote_mutual_bool vars b); crush.
  destruct (constantFolding_mut_nat n); crush.
  destruct (constantFolding_mut_nat n0); crush.
Qed.

(* Exercise 5 : Define mutually inductive typ es of even and o dd natural numb ers, such that any nat-
ural numb er is isomorphic to a value of one of the two typ es. (This problem do es not
ask you to prove that corresp ondence, though some interpretations of the task may b e
interesting exercises.) Write a function that computes the sum of two even numb ers,
such that the function typ e guarantees that the output is even as well. Prove that this
function is commutative. *)

Print nat.
Print list.

Inductive even_nat : Set :=
 | EvZ : even_nat
 | Ev_next : odd_nat -> even_nat
 with odd_nat : Set :=
 | Odd_next : even_nat -> odd_nat.

Fixpoint even_sum (en1 en2 : even_nat) : even_nat :=
  match en1 with
  | EvZ => en2
  | Ev_next od1 => match en2 with
                   | EvZ => en1
                   | Ev_next od2 => Ev_next (Odd_next (odd_sum od1 od2))
                   end                          
  end
with odd_sum (od1 od2 : odd_nat) : even_nat :=
       match od1, od2 with 
       | Odd_next ev1, Odd_next ev2 => Ev_next (Odd_next (even_sum ev1 ev2))
end.                                  

Scheme even_nat_mut := Induction for even_nat Sort Prop
with odd_nat_mut := Induction for odd_nat Sort Prop.

Theorem even_sum_commut : forall (e1 e2 : even_nat),
    even_sum e1 e2 = even_sum e2 e1.
Proof. intros.
       apply (even_nat_mut
                (fun e1 : even_nat => forall e2 : even_nat,
                even_sum e1 e2 = even_sum e2 e1)
                (fun o1 : odd_nat => forall o2 : odd_nat,
                odd_sum o1 o2 = odd_sum o2 o1)
             ); crush. destruct e0; crush. destruct e0; crush. destruct o2; crush. 
Qed.

(* Exercise 6 : Using a reexive inductive definition, define a typ e nat tree of infinitary trees, with
natural numb ers at their leaves and a countable infinity of new trees branching out of
each internal no de. Define a function increment that increments the numb er in every
leaf of a nat tree. Define a function leapfrog over a natural i and a tree nt. leapfrog
should recurse into the i th child of nt, the i +1st child of that no de, the i +2nd child
of the next no de, and so on, until reaching a leaf, in which case leapfrog should return
the numb er at that leaf. Prove that the result of any call to leapfrog is incremented by
one by calling increment on the tree. *)
(*
Inductive rfx_tree : Set :=
| Leaf : nat -> rfx_tree
| Node : nat -> (nat -> rfx_tree) -> rfx_tree.

Example rfx1 : rfx_tree := Leaf 5.
Example rfx2 : rfx_tree := Node 3 (fun x => Leaf x).
Example rfx3 : rfx_tree := Node 3 (fun x => (Node 2 (fun y => Leaf (x*y)))).

Fixpoint increment (rt : rfx_tree) : rfx_tree :=
  match rt with
  | Leaf n => Leaf (S n)
  | Node n f => Node n (fun x => increment (f x))
  end.                 

Fixpoint leapfrog (i : nat) (nt : rfx_tree) : option nat :=
  match nt with
  | Leaf n => match i with
              | O => Some n
              | _ => None
              end         
  | Node n f => match i with
                | O => getNextLeaf nt
                | _ => leapfrog (pred i)                    
                            
 *)

(* Exercise 7 : Define a type of trees of trees of trees of (rep eat to infinity). That is, define an inductive
typ e trexp, whose memb ers are either base cases containing natural numbers or binary
trees of trexp s. Base your definition on a parameterized binary tree typ e btree that you
will also define, so that trexp is defined as a nested inductive type. Define a function
total that sums all of the naturals at the leaves of a trexp. Define a function increment
that increments every leaf of a trexp by one. Prove that, for all tr, total (increment
tr ) ≥ total tr. On the way to finishing this pro of, you will probably want to prove a
lemma and add it as a hint using the syntax Hint Resolve name of lemma..*)
  
Inductive btree (A : Type) : Type :=
  | LeafTree : A -> btree A
  | Node : btree A -> btree A -> btree A.

  (* as a nested inductive type *)
Inductive trexp : Set :=
  | Leaf : nat -> trexp
  | Ctr : btree trexp -> trexp.

Section All.
  Variable T : Set.
  Variable P : T -> Prop.

  Fixpoint All (bt : btree T) : Prop :=
    match bt with
    | LeafTree n => P n
    | Node bt1 bt2 => All bt1 /\ All bt2
    end.                                 
End All.   

Section trexp_ind'.
  Variable P : trexp -> Prop.
  Hypothesis Leaf_case : forall (n : nat),
      P (Leaf n).
  Hypothesis Ctr_case : forall (bt : btree trexp),
      All P bt -> P (Ctr bt).

  Fixpoint trexp_ind' (tr : trexp) : P tr :=
    match tr with
    | Leaf n => Leaf_case n
    | Ctr btr => Ctr_case btr ((fix btree_trexp_ind (btr : btree trexp) : All P btr :=
                                 match btr with
                                 | LeafTree trxp => trexp_ind' trxp
                                 | Node bt1 bt2 => conj (btree_trexp_ind bt1) (btree_trexp_ind bt2)
                                 end) btr
                              ) 
    end.                        (* fix btree_trexp_ind is nested inside the definition *)
End trexp_ind'.
  Section map.
    Variables T T' : Set.
    Variable F : T -> T'.
    Fixpoint map (btr : btree T) : btree T' :=
      match btr with
      | LeafTree n => LeafTree (F n)
      | Node bt1 bt2 => Node (map bt1) (map bt2)
      end.  
  End map.

  Fixpoint sum (btr : btree nat) : nat :=
    match btr with
    | LeafTree n => n
    | Node bt1 bt2 => (sum bt1) + (sum bt2)
    end.                                 
                                             
  Fixpoint total (tr : trexp) : nat :=
    match tr with
    | Leaf n => n
    | Ctr btr => sum (map total btr)
    end.             

  Fixpoint increment (tr : trexp) : trexp :=
    match tr with
    | Leaf n => Leaf (S n)
    | Ctr btr => Ctr (map increment btr)
    end.             

  Example ex1 : trexp := Ctr (Node (LeafTree (Leaf 5)) (LeafTree (Leaf 6)) ).
  Eval simpl in total ex1.
  Eval simpl in increment ex1.
 
  Theorem inc_increases : forall (tr : trexp), total (increment tr) >= total tr.
Check trexp_ind'.
induction tr using trexp_ind'; crush. induction bt; crush. Qed. 

  (* Exercise 8. Prove discrimination and injectivity theorems for the nat_btree type defined earlier in
this chapter. In particular, without using the tactics discriminate, injection, or
congruence, prove that no leaf equals any node, and prove that two equal nodes carry
the same natural number. *)

Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

(* theorem that no leaf equals any node *)
Definition toProp (nbt : nat_btree) := if nbt then True else False.

Theorem node_not_leaf : forall t1 n t2, NLeaf <> NNode t1 n t2.
red. intros. 
change (toProp (NNode t1 n t2)).
rewrite <- H.  simpl. trivial. 
Qed.  

Theorem S_inj' : forall n m : nat, S n = S m -> n = m.
intros n m H.
change (pred (S n) = pred (S m)).
rewrite H.
reflexivity.
Qed.

Definition toTree (n : nat) (t1 t2 : nat_btree) := NNode t1 n t2. (* didn't work with change *)
Definition getN (t : nat_btree) := match t with
                                   | NLeaf => 0
                                   | NNode t1 n t2 => n
                                   end.                      

Theorem btree_inj : forall n m t1 t2, NNode t1 n t2 = NNode t1 m t2 -> n = m.
intros. change (getN (NNode t1 n t2) = getN (NNode t1 m t2)). rewrite H. reflexivity. 
Qed.

(* ========================== FROM PREDICATES will go in separate file. ================================================ *)
(*
Exercise 1. Prove these tautologies of propositional logic, using only the tactics apply, assumption,
constructor, destruct, intro, intros, left, right, split, and unfold.

(a) (True ∨ False ) ∧ (False ∨ True )
(b) P → ¬ ¬ P
(c) P ∧ (Q ∨ R ) → (P ∧ Q ) ∨ (P ∧ R 

will do in separate file
*) 

