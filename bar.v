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

Section decidable_bar_inductive_predicates.

  Variables (X : Type) 
            (T : X -> Prop)        (* T x is for recursive computation is terminated at x *)  
            (R : X -> X -> Prop)   (* R x y means a call on x may generate a recursive sub-call on y*)
            .

  Inductive bar x : Prop :=
    | in_bar_0 : T x -> bar x
    | in_bar_1 : (forall y, R x y -> bar y) -> bar x.

  Hypothesis Tdec : forall x, { T x } + { ~ T x }.  (* we can decide whether computation terminates at x *)

  Variables (P : X -> Type) 
            (HT   : forall x, T x -> P x)                       (* the value when computation is terminated *)
            (Hbar : forall x, (forall y, R x y -> P y) -> P x)  (* from the value of recursive sub-calls, 
                                                                   computes a value of the call *)
            .

  Fixpoint bar_rect x (H : bar x) : P x.
  Proof.
    refine(match Tdec x with
      | left  Hx => HT Hx
      | right Hx => Hbar (fun y Hy => bar_rect y _)
    end).
    destruct H; 
      [ destruct Hx; assumption 
      | apply H, Hy ].
  Defined.

  (* Can this be of any use ? *)

  Variable (pre : X -> Prop) (Hpre : forall x, pre x -> bar x).

  Definition by_bar_induction x : pre x -> P x.
  Proof. intro; apply bar_rect, Hpre, H. Qed. 

End decidable_bar_inductive_predicates.

(* Recursive Extraction bar_rect. *)

Section Acc_bar.

  Variables (X : Type) (T : X -> Prop) (R : X -> X -> Prop).

  Lemma bar_Acc x : bar T R x -> Acc (fun x y => R y x /\ ~ T y) x.
  Proof.
    induction 1 as [ x Hx | x _ Hx ]; constructor.
    intros ? (_ & []); trivial.
    intros y (Hy & _); apply Hx, Hy.
  Qed.
  
  Hypothesis Tdec : forall x, T x \/ ~ T x.

  Lemma Acc_bar_dec x : Acc (fun x y => R y x /\ ~ T y) x -> bar T R x.
  Proof.
    induction 1 as [ x _ Hx ].
    destruct (Tdec x).
    constructor 1; auto.
    constructor 2; intros; apply Hx; tauto.
  Qed.
    
  Theorem bar_Acc_eq_dec x : bar T R x <-> Acc (fun x y => R y x /\ ~ T y) x.
  Proof. split; [ apply bar_Acc | apply Acc_bar_dec ]. Qed.
  
End Acc_bar.

Lemma Acc_antitone X (R1 R2 : X -> X -> Prop) : 
         (forall x y, R1 x y -> R2 x y)
      -> forall x, Acc R2 x -> Acc R1 x.
Proof.
  intros H; induction 1 as [ x _ Hx ]. 
  constructor; intros; apply Hx, H; trivial.
Qed.

Theorem bar_empty_Acc_eq X R x : bar (fun _ : X => False) R x <-> Acc (fun x y => R y x) x. 
Proof.
  rewrite bar_Acc_eq_dec; [ split; apply Acc_antitone; intros | ]; tauto.
Qed.

Section nat_rev_ind.

  Variables (P : nat -> Prop)
            (HP : forall n, P (S n) -> P n).

  Theorem nat_rev_ind x y : x <= y -> P y -> P x.
  Proof. induction 1; auto. Qed.

End nat_rev_ind.

Section Constructive_Epsilon_bar.

  Variable (P : nat -> Prop) (Pdec : forall x, { P x } + { ~ P x }).

  Let R x y := S x = y.

  Let ex_bar0 : ex P -> bar P R 0.
  Proof.
    intros (x & Hx).
    generalize (in_bar_0 _ R _ Hx); apply nat_rev_ind.
    constructor 2; intros ? []; trivial.
    apply le_O_n.
  Qed.

  Theorem Constructive_Epsilon : ex P -> sig P.
  Proof.
    intros H; generalize (ex_bar0 H).
    apply bar_rect with (P := fun _ => _); auto.
    intros x; exists x; auto.
    intros ? Hx; apply Hx with (1 := eq_refl).
  Qed.

  Let CE_full_rec : forall x, bar P R x -> { m | P m /\ forall y, P y -> y < x \/ m <= y }.
  Proof.
    apply bar_rect with (P := fun _ => _); auto.
    intros m; exists m; split; auto; intros; omega.
    intros x Hx.
    destruct (@Hx _ eq_refl) as (m & H1 & H2).
    destruct (Pdec x) as [ H | H ].
    exists x; split; auto; intros; omega.
    exists m; split; auto.
    intros y Hy; specialize (H2 _ Hy).
    destruct (eq_nat_dec x y); subst; (tauto || omega).
  Qed.
  
  (** Constructive Epsilon is a minimization algoritm *)

  Theorem Constructive_Epsilon_full : ex P -> { m |  P m /\ forall y, P y -> m <= y }.
  Proof.
    intros; destruct CE_full_rec with (x := 0) as (m & H1 & H2); auto.
    exists m; split; auto.
    intros y Hy; specialize (H2 _ Hy); omega.
  Qed.

End Constructive_Epsilon_bar.