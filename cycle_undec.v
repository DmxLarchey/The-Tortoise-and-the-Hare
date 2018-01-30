(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega.

Require Import utils.

Set Implicit Arguments.

Section cycle_existence_undec.

  (** This is a computable reduction of the halting problem to the cycle detection problem 
      hence a proof that cycle detection is an undecidable problem
   *)

  (** We suppose that there is a complete cycle detection algo. *)

  Hypothesis cycle_dec : forall X (eq_X_dec : forall x y : X, { x = y } + { x <> y })
                                (f : X -> X) (x0 : X), {   exists τ, 0 < τ /\ f↑τ x0 = f↑(2*τ) x0 }
                                                     + { ~ exists τ, 0 < τ /\ f↑τ x0 = f↑(2*τ) x0 }.

  (** And we show that we can solve the halting problem, obtaining an impossibility

      We consider a state machine (for instance a Turing machine or
      a Minsky machine) with a state transition function that
      maps a state to either finished or error or a new state.

      In these models, equality between states can be decided

      We show that we can decide whether a computation
      finishes in a finite number of steps or not

   *)

  Inductive stop : Set := finished | error.

  Variable (state : Type) 
           (state_eq_dec : forall s1 s2 : state, { s1 = s2 } + { s1 <> s2 })
           (next : state -> stop + state).

  Fixpoint compute n (s : state) : stop + state :=
    match n with 
      | 0   => inr s
      | S n => match compute n s with
        | inl e  => inl e
        | inr s' => next s'
      end
    end.

  (* The halting problem: given a starting state s, is
       the finished state reached within a finite number of
       steps.

     This problem is known to be undecidable for Turing or
       Minsky machines (we do not provide a proof for this)
   *)

  Definition halts s := exists n, compute n s = inl finished.

  Let X : Type := unit + (nat * (unit+state)).

  Let eq_X_dec (u v : X) : { u = v } + { u <> v }.
  Proof.
    do 4 decide equality.
  Qed.

  Let f (x : X) :=
    match x with
      | inl _ => inl tt
      | inr (n,inl _) => inr (S n,inl tt)
      | inr (n,inr s) => match next s with
        | inl finished => inl tt
        | inl error    => inr (S n,inl tt)
        | inr s'       => inr (S n,inr s')
      end
    end.

  Section f_compute.

    Let Hf1 n s : match compute n s with
                           | inl finished => f↑n (inr (0,inr s)) = inl tt
                           | inl error    => f↑n (inr (0,inr s)) = inr (n,inl tt)
                           | inr s'       => f↑n (inr (0,inr s)) = inr (n,inr s')
                         end.
    Proof.
      induction n as [ | n IHn ]; simpl; auto.
      destruct (compute n s) as [ [] | s' ].
      rewrite IHn; auto.
      rewrite IHn; auto.
      rewrite IHn; unfold f.
      destruct (next s') as [ [] | ]; auto.
    Qed.
  
    Let Hf2 n m s : match f↑n (inr (m,inr s)) with
                           | inl _          => compute n s = inl finished
                           | inr (k,inl _)  => k = n+m /\ compute n s = inl error
                           | inr (k,inr s') => k = n+m /\ compute n s = inr s'
                         end.
    Proof.
      induction n as [ | n IHn ]; simpl; auto.
      destruct (f ↑ n (inr (m, inr s))) as [ [] | (k & [ [] | s' ]) ]; unfold f; simpl.
      rewrite IHn; auto.
      destruct IHn as (? & IHn); subst k; rewrite IHn; auto.
      destruct IHn as (? & IHn); subst k; rewrite IHn; auto.
      destruct (next s') as [ [] | ]; auto.
    Qed.

    Let Hf3 n m k s s' : f↑n (inr (m,inr s)) = inr (k,s') -> k = n+m.
    Proof.
      intros H; generalize (Hf2 n m s); rewrite H.
      destruct s'; intros []; auto.
    Qed.

    Local Fact f_compute s n u : f↑n (inr (0,inr s)) = inl u <-> compute n s = inl finished.
    Proof.
      split; intros H.
      generalize (Hf2 n 0 s); rewrite H; auto.
      generalize (Hf1 n s); rewrite H; destruct u; auto.
    Qed.

    Local Fact f_cycle s i j : i <> j -> f↑i (inr (0,inr s)) = f↑j (inr (0,inr s)) -> f↑i (inr (0,inr s)) = inl tt.
    Proof.
      intros H1 H2.
      case_eq (f ↑ i (inr (0, inr s))).
      intros []; auto.
      intros (n & [ [] | s' ]) H;
      rewrite H in H2; symmetry in H2;
      apply Hf3 in H2; apply Hf3 in H; omega.
    Qed.

  End f_compute.

  Theorem halting_problem_dec s : { halts s } + { ~ halts s }.
  Proof.
    destruct (cycle_dec eq_X_dec f (inr (0,inr s))) 
      as [ H | H ].

    left.
    destruct H as (m & H1 & H2).
    assert (m <> 2*m) as H3 by omega.
    generalize (f_cycle _ H3 H2); intros H.
    apply f_compute in H; exists m; auto.

    right.
    intros (n & Hn).
    rewrite <- f_compute with (u := tt) in Hn.
    apply H.
    do 3 apply cyclicity_prop.
    exists n, (S n).
    split; auto.
    simpl; rewrite Hn; auto.
  Qed.

End cycle_existence_undec.

Print stop.
Check halting_problem_dec.
Print Assumptions halting_problem_dec.
