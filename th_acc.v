(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega.

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

Fact iter_plus X f a b (x : X) : f↑(a+b) x = f↑a (f↑b x).
Proof. induction a; simpl; f_equal; auto. Qed.

Tactic Notation "rew" "iter" constr(f) :=
  repeat match goal with 
    | |- context[f ?x]           => change (f x) with (f↑1 x)
    | |- context[f↑?a (f↑?b ?x)] => rewrite <- (iter_plus f a b)
  end.

Section Tortoise_and_Hare_tail_recursive.

  Variables (X : Type) (eqdec : forall x y : X, { x = y } + { x <> y }).
  
  Infix "=?" := eqdec (at level 70).

  Variable (f : X -> X) (x0 : X) 
           (Hx0 : exists τ, 0 < τ /\ f↑τ x0 = f↑(2*τ) x0).

  Let R (c d : X*X) := match d with (x,y) => x<>y /\ c = (f x, f (f y)) end.

  Let tortoise_hare_tail_rec : 
    forall i x y, Acc R (x,y) -> { k | i <= k /\ f↑(k-i) x = f↑(2*(k-i)) y }.
  Proof.
    refine (fix loop i x y H { struct H } := 
           match x =? y with
             | left E  => exist _ i _
             | right C => match loop (S i) (f x) (f (f y)) _ with
                            | exist _ k Hk => exist _ k _
                          end
           end).
    * split; f_equal; auto; omega.
    * apply Acc_inv with (1 := H); constructor; trivial.
    * destruct Hk; split; try omega.
      revert H1; rew iter f; intros H1.
      eq goal with H1; do 2 f_equal; omega.
  Qed.

  Let Acc_eq x y : x = y -> Acc R (x,y).
  Proof.
    intros; constructor 1.
    intros [] (? & _); tauto.
  Qed.

  Let Acc_f0_ff0 : Acc R (f x0, f (f x0)).
  Proof.
    destruct Hx0 as (k & H1 & H2).
    apply Acc_eq in H2.
    revert k H1 H2; apply nat_rev_ind. 
    intros ? H.
    constructor 1.
    intros (u,v) (_ & Huv).
    inversion Huv; subst.
    rew iter f; eq goal with H; do 3 f_equal; omega.
  Qed.

  Definition tortoise_hare_tail : { τ | 0 < τ /\ f↑τ x0 = f↑(2*τ) x0 }.
  Proof.
    refine (match tortoise_hare_tail_rec 1 Acc_f0_ff0 with
      | exist _ k Hk => exist _ k _
    end).
    destruct Hk as (? & Hk); split; try omega.
    revert Hk; rew iter f; intros Hk.
    eq goal with Hk; do 2 f_equal; omega.
  Defined.

End Tortoise_and_Hare_tail_recursive.

Recursive Extraction tortoise_hare_tail.
