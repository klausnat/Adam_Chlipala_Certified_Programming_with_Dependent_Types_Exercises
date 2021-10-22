(* begin hide *)
Set Implicit Arguments.
Set Asymmetric Patterns.
Require Import Cpdt.CpdtTactics.
Require Import List. 
(* end hide *)

(* 0.5 From MoreDep *)
(*
1. Define a kind of dependently typed lists, where a list's type index gives a lower bound on
how many of its elements satisfy a particular predicate. In particular, for an arbitrary
set A and a predicate P over it:
 *)

(* Defining A KIND : 

regular list : type => type
plist        : nat => type *)
    
(*
(a) Define a type plist : nat → Set. Each plist n should be a list of As, where it
is guaranteed that at least n distinct elements satisfy P. There is wide latitude
in choosing how to encode this. You should try to avoid using subset types or
any other mechanism based on annotating non-dependent types with propositions
after-the-fact. *)

Section plist.
  Variable A : Set.
  Variable P : A -> Prop.
  Variable dec : forall x, {P x} + {~ P x}.
  
  Inductive plist : nat -> Set :=
  | PNil : plist O
  | PCons_no : forall n, A -> plist n -> plist n
  | PCons_yes : forall n (x : A), P x -> plist n -> plist (S n).

  Print list.                   (* Inductive list (A : Type) : Type *)
Print plist.   
(*
(b) Define a version of list concatenation that works on plist s. The type of this new
function should express as much information as possible about the output plist. *)
Fixpoint app n1 (ls1 : plist n1) n2 (ls2 : plist n2) : plist (n1 + n2) :=
  match ls1 in (plist n1) return plist (n1 + n2) with
  | PNil => ls2
  | PCons_no _ x ls1' => PCons_no x (app ls1' ls2 )
  | @PCons_yes n x px ls1' => @PCons_yes _ _ px (app ls1' ls2)
  end.                                   

(*
(c) Define a function plistOut for translating plists to normal lists. *)

Fixpoint plistOut n (pl : plist n) : list A :=
  match pl with
  | PNil => nil
  | PCons_no _ x pl' => x :: (plistOut pl')
  | @PCons_yes _ x _ pl' => x :: (plistOut pl')
  end.                          

(*
(d) Define a function plistIn for translating lists to plists. The type of plistIn should
make it clear that the best bound on P -matching elements is chosen. You may
assume that you are given a dependently typed function for deciding instances of
P. *)

Fixpoint p_len (pl : list A) : nat :=
  match pl with
  | nil => 0
  | x :: xs => if (dec x) then (S (p_len xs)) else (p_len xs)
  end.                                                  

Definition plistIn (ls0 : list A) : plist (p_len ls0).
  refine(let fix f (ls : list A) : plist (p_len ls) :=
             match ls as ls' return (plist (p_len ls')) with
             | nil => PNil
             | x :: xs => match dec x as d
                                return plist (if d then (S (p_len xs))
                                              else p_len xs) with
                          | left px => PCons_yes px (f xs)
                          | right _ => PCons_no x (f xs)
                          end
             end in f ls0
        ).
Defined.        
  
(*
(e) Prove that, for any list ls, plistOut (plistIn ls ) = ls. This should be the only part
of the exercise where you use tactic-based proving. *)

Lemma convert_correct : forall ls, plistOut (plistIn ls) = ls.
  induction ls.
  - crush. 
  - simpl. destruct (dec a); simpl; crush. 
Qed. 

(*
(f ) Define a function grab : ∀ n (ls : plist (S n )), sig P. That is, when given a
plist guaranteed to contain at least one element satisfying P, grab produces such
an element. The type family sig is the one we met earlier for sigma types (i.e.,
dependent pairs of programs and proofs), and sig P is extensionally equivalent
to {x : A | P x }, though the latter form uses an eta-expansion of P instead of P
itself as the predicat *)

(* Inductive sig (A : Type) (P : A -> Prop) : Type :=  exist : forall x : A, P x -> {x : A | P x} 

Inductive plist : nat -> Set :=
  | PNil : plist O
  | PCons_no : forall n, A -> plist n -> plist n
  | PCons_yes : forall n (x : A), P x -> plist n -> plist (S n).
 *)


Definition grab n (ls0 : plist (S n)) : sig P.
  refine (let fix f n (ls : plist (S n)) : sig P :=
              match ls in (plist (S n)) return (sig P) with
              | PCons_no n x pl => f _ _
              | PCons_yes _ x px _ => exist x px
              end in f n ls0
         ).
  apply f in ls; auto. apply f in ls; auto. 
Defined.

Fixpoint grab n (ls : plist (S n)) : sig P.
  match ls in (plist (S n)) return (sig P) with
  | @PCons_no (S n) _ pl' => grab n pl'
  | @PCons_no 0 _ pl' => _
  | @PCons_yes _ x px _ => exist x px
  end.                               









  
  

