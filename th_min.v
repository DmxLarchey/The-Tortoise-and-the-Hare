(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega.

Require Import bar.

Set Implicit Arguments.

Tactic Notation "eq" "goal" "with" hyp(H) := 
  match goal with |- ?b => match type of H with ?t => replace b with t; auto end end.
  
Theorem nat_rev_ind (P : nat -> Prop) (HP : forall n, P (S n) -> P n) x y : x <= y -> P y -> P x.
Proof. induction 1; auto. Qed.

Reserved Notation "f ↑ n" (at level 1, left associativity).

Fixpoint iter X (f : X -> X) n x :=
  match n with 
    | 0 => x
    | S n => f (f↑n x)
  end
where "f ↑ n" := (@iter _ f n).

Section th_min.

  Variables (X : Type) (eqdec : forall x y : X, { x = y } + { x <> y }).
  
  Infix "=?" := eqdec (at level 70).

  Variable (f : X -> X) (x0 : X) 
           (Hx0 : exists τ, 0 < τ /\ f↑τ x0 = f↑(2*τ) x0).

  Theorem th_min : { τ | 0 < τ /\ f↑τ x0 = f↑(2*τ) x0 }.
  Proof.
    apply Constructive_Epsilon; trivial.
    intros n.
    destruct (le_lt_dec n 0) as [ | H ]; [right; omega | ].
    destruct (eqdec (f↑n x0) (f↑(2*n) x0)); tauto.
  Qed.
  
End th_min.

Extraction Inline bar_rect.
Extraction Inline Constructive_Epsilon.
Recursive Extraction th_min.