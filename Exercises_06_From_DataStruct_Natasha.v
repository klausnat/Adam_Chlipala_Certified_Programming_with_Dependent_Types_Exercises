(* begin hide *)
Set Implicit Arguments.
Set Asymmetric Patterns.
Require Import Cpdt.CpdtTactics.
Require Import List. 
(* end hide *)

(* 06. FROM DATA STRUCT *)

(* Some of the type family definitions and associated functions from this chapter are dupli-
cated in the DepList module of the book source. Some of their names have been changed to
be more sensible in a general context. *)

(*
1. Define a tree analogue of hlist. That is, define a parameterized type of binary trees with
data at their leaves, and define a type family htree indexed by trees. The structure of
an htree mirrors its index tree, with the type of each data element (which only occur
at leaves) determined by applying a type function to the corresponding element of the
index tree. *)

Section htree.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive tree (T : Type) : Type :=
  | Leaf : T -> tree T
  | Node : tree T -> tree T -> tree T.                   

  Inductive htree : tree A -> Type :=
  | HLeaf : forall (x : A), B x -> htree (Leaf x)
  | HNode : forall (tr1 : tree A) (tr2 : tree A), htree tr1 ->
                                                  htree tr2 ->
                                                  htree (Node tr1 tr2).

(* Define a type standing for all possible paths from the root of a tree to
leaves and use it to implement a function tget for extracting an element of an htree
by path. *)

 Variable elm : A.

 Inductive membert : tree A -> Type :=
 | HThis : membert (Leaf elm)
 | HLeft : forall tr1 tr2, membert tr1 -> membert (Node tr1 tr2)
 | HRight : forall tr1 tr2, membert tr2 -> membert (Node tr1 tr2).     

 Print Empty_set. 
(*
Fixpoint tget tr (mtr : htree tr) : membert tr -> B elm :=
  match mtr with
  | HLeaf _ bx => fun mem => (match mem in membert (Leaf h) return (B h -> B elm) with
                             | HThis => fun x => x
                             | _ => fun x => x
                             end) bx
  | HNode t1 t2 Ht1 Ht2 => fun mem => match mem in membert tr' return (match tr' with
                                                                      | Leaf _ => unit
                                                                      | Node lt rt =>
                                                                        (membert lt -> B elm) ->
                                                                        (membert rt -> B elm) ->
                                                                        B elm
                                                                      end) with
                                      | HThis => tt
                                      | HLeft _ _ meml => tget t1 _ Ht1
                                      | HRight _ _ memr => tget t2 _ Ht2
                                      end  
  end.                                        
*)
End htree. 

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).    

  Variable elm : A. 

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).
  (* получает 
     ls - список эл-в типа A (ANat | ABool) 
     mls : hlist ls
     возвращает (B elm) - элемент типа nat, 3, например *)
   
  Fixpoint hget ls (mls : hlist ls) : member ls -> B elm :=
    match mls with
      | HNil => match


End hlist.         

(* Example of HList by Adam Chlipala, from the book *)
Arguments HNil {A B}.
Arguments HCons {A B x ls}.
Arguments HFirst {A elm ls}.
Arguments HNext {A elm x ls}.

Definition someTypes : list Set := nat :: bool :: nil. 
Example someValues : hlist (fun T : Set => T) someTypes := HCons 5 (HCons true HNil).

Eval simpl in hget someValues HFirst. 
Eval simpl in hget someValues (HNext HFirst). 

Example somePairs : hlist (fun T : Set => T * T)%type someTypes := HCons (1,2) (HCons (true, false)HNil).

(* Example of hlist by Natasha*)
Inductive atype := ANat | ABool. (*  elements of type A  *)

Definition b_type : atype -> Type := (*  function B  *)
  fun x => match x with
           | ANat => nat
           | ABool => bool
           end.              

Check HCons.
Check (@HCons atype b_type ANat nil 3 (@HNil atype b_type)).
Check @HCons atype b_type ABool (ANat :: nil) true (@HCons atype b_type ANat nil 3 (@HNil atype b_type)).

(* Define a function htmap2 for "mapping over two trees in parallel." That is,
htmap2 takes in two htrees with the same index tree, and it forms a new htree with
the same index by applying a binary function pointwise.
Repeat this process so that you implement each definition for each of the three defini-
tion styles covered in this chapter: inductive, recursive, and index function.
 *)
