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

Section Tortoise_and_Hare.

  Variables (X : Type) (eqdec : forall x y : X, { x = y } + { x <> y }).
  
  Infix "=?" := eqdec (at level 70).

  Variable (f : X -> X) (x0 : X) 
           (Hx0 : exists τ, 0 < τ /\ f↑τ x0 = f↑(2*τ) x0).
  
  (** The custom bar inductive predicate that serves as termination
      criteria for tortoise_hare_rec *)
  
  Inductive bar_th x y : Prop :=
    | in_bar_th_0 : x = y                  -> bar_th x y 
    | in_bar_th_1 : bar_th (f x) (f (f y)) -> bar_th x y.
    
  (** We give the explicit computational part using refine 
      and the proof of the logical part is delayed using _ 
  *)
  
  Fixpoint tort_hare_rec x y (H : bar_th x y) : { τ | f↑τ x = f↑(2*τ) y }.
  Proof.
    refine (match x =? y with
             | left E  => exist _ 0 _
             | right C => let (k,Hk) := tort_hare_rec (f x) (f (f y)) _ 
                          in  exist _ (S k) _
           end).
    * auto.
    * inversion H; tauto.
    * finish with Hk.
  Defined.

  (** Now we fix a starting point for which the iterations 
      of f ends into a non-empty loop, we use Hx0 *)
  
  Let bar_th_fx0_ffx0 : bar_th (f x0) (f (f x0)).
  Proof.
    destruct Hx0 as (k & H1 & H2).
    apply in_bar_th_0 in H2.
    revert k H1 H2; apply nat_rev_ind. 
    intros ? H; apply in_bar_th_1; finish with H.
  Qed.
  
  Definition tortoise_hare : { τ | 0 < τ /\ f↑τ x0 = f↑(2*τ) x0 }.
  Proof.
    refine (match tort_hare_rec bar_th_fx0_ffx0 with
      | exist _ k Hk => exist _ (S k) _
    end).
    split; try omega; finish with Hk.
  Defined.

  Let tortoise_hare_tail_rec : 
    forall i x y, bar_th x y -> { k | i <= k /\ f↑(k-i) x = f↑(2*(k-i)) y }.
  Proof.
    refine (fix loop i x y H { struct H } := 
           match x =? y with
             | left E  => exist _ i _
             | right C => match loop (S i) (f x) (f (f y)) _ with
                            | exist _ k Hk => exist _ k _
                          end
           end).
    * split; f_equal; auto; omega.
    * inversion H; tauto.
    * destruct Hk; split; try omega; finish with H1.
  Qed.

  Definition tortoise_hare_tail : { τ | 0 < τ /\ f↑τ x0 = f↑(2*τ) x0 }.
  Proof.
    refine (let (k,Hk) := tortoise_hare_tail_rec 1 bar_th_fx0_ffx0 in exist _ k _).
    destruct Hk as (? & Hk); split; try omega.
    finish with Hk.
  Defined.

End Tortoise_and_Hare.

Check tortoise_hare.
Print Assumptions tortoise_hare.
Recursive Extraction tortoise_hare.

Check tortoise_hare_tail.
Print Assumptions tortoise_hare_tail.
Extraction tortoise_hare_tail.
