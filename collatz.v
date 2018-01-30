(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega (* utils *).

Set Implicit Arguments.

Definition decidable (P : Prop) := { P } + { ~ P }.

Section decidable_option.

  Variable (X : Type) (eq_X_dec : forall x y : X, decidable(x = y)).
  
  Fact decidable_option : forall x y : option X, decidable(x = y).
  Proof.
    intros [ x | ] [ y | ]; red; ((right; discriminate) || (left; reflexivity) || idtac).
    destruct (eq_X_dec x y) as [ | C ]; [ left; subst; auto | ].
    right; contradict C; injection C; auto.
  Defined.

End decidable_option.

Parameter epsilon : (nat -> Prop) -> nat.
Axiom epsilon_spec : forall P, ex P -> P (epsilon P).

Section reif.
  
  Definition nat_prop_reify (P : nat -> Prop) : ex P -> sig P.
  Proof.
    exists (epsilon P); apply epsilon_spec; auto.
  Defined.
  
  Definition nat_rel_reify (R : nat -> nat -> Prop) : (forall n, exists i, R n i) -> { f | forall n, R n (f n) }.
  Proof.
    intros H.
    assert (forall n, { i | R n i }) as H1.
      intro; apply nat_prop_reify, H.
    exists (fun n => proj1_sig (H1 n)).
    intro n; apply (proj2_sig (H1 n)).
  Defined.
  
  Theorem disj_reify (P Q : Prop) : P \/ Q -> { P } + { Q }.
  Proof.
    intros H1.
    set (f n := match n with 0 => P | _ => Q end).
    destruct (@nat_prop_reify f) as ([ | n] & Hn).
    destruct H1; [ exists 0 | exists 1 ]; auto.
    left; auto.
    right; auto.
  Defined.
  
End reif.

Section decidable_re2.

  Variables (P : nat -> nat -> Prop) (Pdec : forall x y, decidable (P x y)).
  
  Theorem decidable_re2 x : decidable (exists y, P x y).
  Proof.
    destruct (Pdec x (epsilon (P x))) as [ H | H ].
    left; exists (epsilon (P x)); auto.
    right; contradict H; revert H; apply epsilon_spec.
  Defined.
  
End decidable_re2.

Section decidable_re1.

  Variables (P : nat -> Prop) (Pdec : forall x, decidable (P x)).
  
  Theorem decidable_re1 : decidable (exists y, P y).
  Proof.
    set (Q (_ : nat) y := P y).
    destruct (decidable_re2 Q) with (x := 0).
    intros; apply Pdec.
    left; auto.
    right; tauto.
  Defined.
  
End decidable_re1.

Section halting_problem.

  Implicit Type R : nat -> nat -> Prop.
  
  (** If R : nat -> nat -> Prop is a recursive function, then there exists a
      predicate f : nat -> nat -> option nat (an operational semantics for the algo. of R)
      such that a) and b) are equivalent:
      
        a) R n v               (R compute v from n)
        b) exists i, f n i v   (f compute v from n in i steps, for some i)
     
     See "Typing Total Recursive Functions in Coq" by DLW
        
   *) 

  Definition recursive R := exists f : nat -> nat -> option nat, forall n v, R n v <-> exists i, f n i = Some v .
  Definition is_halting_on R n := exists i, R n i.
  
  (** Using epsilon, one can solve the halting problem ... 
  
      This does not necesseraly lead to a contradiction in Coq but it implies
      that assuming epsilon/epsilon_spec as axioms introduces non-computable functions in Coq
  *)
  
  Theorem Halting_problem R : recursive R -> forall n, decidable (is_halting_on R n).
  Proof.
    intros HR n.
    apply disj_reify.
    destruct HR as (f & Hf).
    destruct decidable_re2 with (P := fun n v => exists i, f n i = Some v)
                                (x := n) 
      as [ H | H ].
      
    intros; simpl; apply decidable_re2 with (P := fun u v => f u v = Some y).
    intros; apply decidable_option, eq_nat_dec. 
    
    left.
    destruct H as (v & H).
    exists v; rewrite Hf; auto.
    
    right; contradict H.
    destruct H as (v & H).
    rewrite Hf in H.
    exists v; auto.
  Defined.

End halting_problem.

Reserved Notation "f ↑ n" (at level 1, left associativity).

Fixpoint iter X (f : X -> X) n x :=
  match n with 
    | 0 => x
    | S n => f (f↑n x)
  end
where "f ↑ n" := (@iter _ f n).

Section collatz.

  (** f is an arbitray map nat -> nat and e an arbitrary nat
  
      for instance f could be the Collatz function 
         1) f n => n div 2  (if n is even)
         2/ f n => 3*n+1    (if n is odd)
      and e could be 1
      
   *)

  Variable (f : nat -> nat) (e : nat).
  
  Let lemma1 n : { i | f↑i n = e } + { forall i, f↑i n <> e }.
  Proof.
    destruct decidable_re2 with (x := n) (P := fun n i => f↑i n = e) as [ H | H ].
    unfold decidable; intros x y; generalize (eq_nat_dec (f↑y x) e); simpl; tauto.
    apply nat_prop_reify in H; auto.
    right; intros i.
    destruct (eq_nat_dec (f↑i n) e); auto.
    contradict H; exists i; auto.
  Qed.
  
  (** Using epsilon_spec, we can derive a program that outputs either
        a/ a number n such that the iteration of f over n never reach e
        b/ a function g which computes, for any input n, a number of
           steps for the iteration of f over n to reach e
           
        Applying this function to the Collatz function would solve
        the Collatz conjecture ...
   *)
  
  Theorem decidable_collatz : { n | forall i, f↑i n <> e } + { g | forall n, f↑(g n) n = e }.
  Proof.
    set (P n := forall i, f↑i n <> e).
    destruct (decidable_re1 P) as [ H | H ].
    
    intros n; red; unfold P.
    destruct (lemma1 n) as [ (i & Hi) | H ]; auto.
    right; intros C; apply (C _ Hi).
    
    left; apply nat_prop_reify; auto.
    
    right.
    apply nat_rel_reify with (R := fun x y => f↑y x = e).
    intros n.
    unfold P in H.
    destruct (lemma1 n) as [ (i & Hi) | H1 ].
    exists i; auto.
    contradict H.
    exists n; auto.
  Defined.
  
End collatz.

Check decidable_collatz.
Print Assumptions decidable_collatz.

Check Halting_problem.
Print Assumptions Halting_problem.
     