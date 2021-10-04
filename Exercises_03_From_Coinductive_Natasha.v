(* begin hide *)
Set Implicit Arguments.
Require Import Cpdt.CpdtTactics.
Require Export Coq.Strings.String.
Require Import Bool. 
(* end hide *)

(*
03. From Coinductive.

1. (a) Define a co-inductive type of infinite trees carrying data of a fixed parameter type.
Each node should contain a data value and two child trees.
 *)

Section tree.
  
  Variable A : Type.
  CoInductive tree : Type :=
  | Node : tree -> A -> tree -> tree.

(*
(b) Define a function everywhere for building a tree with the same data value at every
node. *)
  
CoFixpoint everywhere (v : A) : tree := Node (everywhere v) v (everywhere v).
  
End tree.

(* 
(c) Define a function map for building an output tree out of two input trees by travers-
ing them in parallel and applying a two-argument function to their corresponding
data values.
 *)

Section map.
  Variables A B C : Type.
  Variable f : A -> B -> C.
  CoFixpoint map (t1 : tree A) (t2 : tree B) : tree C :=
    match (t1, t2) with
    | ((Node t1' a t1''), (Node t2' b t2'')) => Node (map t1' t2') (f a b) (map t1'' t2'')
    end.
End map.

(* (d) Define a tree falses where every node has the value false. *)

Definition falses := everywhere false.

(* (e) Define a tree true_false where the root node has value true, its children have value
false, all nodes at the next have the value true, and so on, alternating boolean
values from level to level. *)

CoFixpoint true_false : tree bool := Node false_true true false_true
with false_true : tree bool := Node true_false false true_false.

(* (f ) Prove that true_false is equal to the result of mapping the boolean "or" function
orb over true_false and falses. You can make orb available with Require Import
Bool.. You may find the lemma orb_false_r from the same module helpful. Your
proof here should not be about the standard equality =, but rather about some
new equality relation that you define. *)

        
CoInductive trees_eq : tree bool -> tree bool -> Prop :=
| Trees_eq : forall t1' t1'' t2' t2'' x y,
    eq x y ->
    trees_eq t1' t2' ->
    trees_eq t1'' t2'' ->
    trees_eq (Node t1' x t1'') (Node t2' y t2'').

Definition frob (t : tree bool) : tree bool :=
  match t with
  | Node t1 x t2 => Node t1 x t2
  end.                        

Theorem frob_eq : forall t : tree bool, t = frob t.
destruct t. simpl. reflexivity. Qed. 
    (* Frob didn't help below abowe. So we try to create co_induction principle according to book 
Lemma F_case : trees_eq true_false ( map orb true_false falses ).
  cofix trees_eq.
  rewrite (frob_eq true_false) at 1.
  rewrite (frob_eq (map orb true_false falses)).
  simpl. 
  constructor.
  - reflexivity.
  - cofix trees_eq'.
    rewrite (frob_eq false_true) at 1.
    rewrite (frob_eq (((cofix map (t1 t2 : tree bool) : tree bool :=
        match t1 with
        | Node t1' a t1'' =>
            match t2 with
            | Node t2' b t2'' => Node (map t1' t2') (a || b) (map t1'' t2'')
            end
        end) false_true
       ((cofix everywhere (v : bool) : tree bool := Node (everywhere v) v (everywhere v)) false)))).
    simpl.
    constructor.
    + reflexivity.
    + assumption.
    + assumption.
  - cofix trees_eq'.
    rewrite (frob_eq false_true) at 1.
    rewrite (frob_eq (((cofix map (t1 t2 : tree bool) : tree bool :=
        match t1 with
        | Node t1' a t1'' =>
            match t2 with
            | Node t2' b t2'' => Node (map t1' t2') (a || b) (map t1'' t2'')
            end
        end) false_true
       ((cofix everywhere (v : bool) : tree bool := Node (everywhere v) v (everywhere v)) false)))).
    simpl.
    constructor.
    + reflexivity.
    + assumption.
    + assumption.
Qed.     *)
    
    (* Frob didn't help abowe. So we try to create co_induction principle according to book *)

Definition mdl A (t : tree A) : A :=
  match t with
  | Node _ x _ => x
  end.                    

Definition left_tree A (t : tree A) : tree A :=
  match t with
  | Node lt _ _ => lt
  end.                    

Definition right_tree A (t : tree A) : tree A :=
  match t with
  | Node _ _ rt => rt
  end.

Section tree_eq_coind.
  Variable R : tree bool -> tree bool -> Prop.
  Hypothesis Node_case_mdl : forall t1 t2, R t1 t2 -> mdl t1 = mdl t2.
  Hypothesis Node_case_left_tree : forall t1 t2, R t1 t2 -> R (left_tree t1) (left_tree t2).
  Hypothesis Node_case_right_tree : forall t1 t2, R t1 t2 -> R (right_tree t1) (right_tree t2).

  Theorem tree_eq_coind : forall t1 t2, R t1 t2 -> trees_eq t1 t2.
    cofix tree_eq_coind; destruct t1; destruct t2; intro.
    generalize (Node_case_mdl H). intro Heq; simpl in Heq; rewrite Heq.
    constructor; auto.
    apply Node_case_left_tree in H. simpl in H. 
    apply tree_eq_coind in H. auto. 
    apply Node_case_right_tree in H.
    apply tree_eq_coind in H. auto. 
  Qed. 
End tree_eq_coind. 

Print tree_eq_coind. 

(* final lemma : exercise (f) *)
Lemma F_case : trees_eq true_false ( map orb true_false falses ).
  apply (tree_eq_coind (fun t1 t2 => (t1 = true_false /\
                                      t2 = (map orb true_false falses)) \/
(t1 = false_true /\ t2 = (map orb false_true falses))
        )); crush.
Qed. 


  (* Helping 
Print orb_false_r.
  
orb_false_r = 
fun b : bool => if b as b0 return (b0 || false = b0) then eq_refl else eq_refl
     : forall b : bool, b || false = b

Arguments orb_false_r _%bool_scope

*)
