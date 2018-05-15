(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Euclid Omega Relations.

Require Import utils brent_common.

Set Implicit Arguments.

Local Infix "div" := (nat_divides) (at level 70). 

(** This is an implementation of Brent's period finding
    algorithm. It extracts to something like the following OCaml code

    let brent f x0 =
      let rec loop p l x y =
        if      x = y then l
        else if p = l then loop (2*p) 1    y (f y)
        else               loop    p (1+l) x (f y)
    in loop 1 1 x0 (f x0);;

    Please notice that to be efficient, the implementation should
    use a binary representation of nats so that 2*p is computed by shifting
    and equality test p = l is log and not linear ... 

    For unary nats, the trick is to store p+l-1 and (p-l) into accumulators 
    to avoid having to multiply p by two and avoid comparing l with p but 
    instead compare (p-l) with 0 (by pattern matchin).

      --> This is done in brent_una.v
*)

Section Brent.

  Variables (X : Type) (eqdec : forall x y : X, { x = y } + { x <> y })
            (f : X -> X) (x0 : X) (Hx0 : exists τ, 0 < τ /\ f↑τ x0 = f↑(2*τ) x0).
           
  Infix "=?" := eqdec (at level 70).
  
  (** The custom bar inductive predicate that serves as termination
      criteria for Brent's algorithm *)
    
  Inductive bar_br : nat -> nat -> X -> X -> Prop :=
    | in_bar_br_0 : forall p l x,            bar_br p l x x 
    | in_bar_br_1 : forall p x y,            bar_br (2*p) 1 y (f y) 
                                          -> bar_br p p x y
    | in_bar_br_2 : forall p l x y, l < p -> bar_br p (S l) x (f y)
                                          -> bar_br p l x y.

  Let lex_bar_br_0 p l x y n : n+l <= p -> bar_br p (n+l) x (f↑n y) -> bar_br p l x y.
  Proof.
    revert p l x y; induction n as [ | n IHn ]; intros p l x y; simpl; auto; intros Hn H.
    constructor 3; try omega.
    apply IHn; try omega.
    eq goal with H; f_equal; try omega.
    rewrite <- (iter_plus f _ 1), plus_comm; auto.
  Qed.

  Let lex_bar_br_1 p l1 l2 :
         l1 <= l2 <= pow2 p
      -> bar_br (pow2 p) l2 (f↑(pow2 p-1) x0) (f↑(l2+pow2 p-1) x0)
      -> bar_br (pow2 p) l1 (f↑(pow2 p-1) x0) (f↑(l1+pow2 p-1) x0).
  Proof.
    intros H1 H2.
    apply lex_bar_br_0 with (n := l2 - l1); try omega.
    eq goal with H2; f_equal; try omega.
    rewrite <- iter_plus; f_equal; omega.
  Qed.

  Let lex_bar_br p1 l1 p2 l2 : 
         (p1 < p2 \/ p1 = p2 /\ l1 <= l2)
      -> 1 <= l1 <= pow2 p1
      -> 1 <= l2 <= pow2 p2
      -> bar_br (pow2 p2) l2 (f↑(pow2 p2-1) x0) (f↑(l2+pow2 p2-1) x0)
      -> bar_br (pow2 p1) l1 (f↑(pow2 p1-1) x0) (f↑(l1+pow2 p1-1) x0).
   Proof.
    intros H1 H3 H4.
    assert (p1 <= p2) as H by omega.
    revert H l1 l2 H1 H3 H4.
    induction 1 as [ | p2 H IH ].
    * intros l1 l2 [ H1 | (H1 & H2) ] (H3 & _) (_ & H4).
      + exfalso; omega.
      + apply lex_bar_br_1; auto.
    * intros l1 l2 _ H3 H4 H5.
      apply IH with (l2 := pow2 p2); auto.
      + destruct (le_lt_dec p2 p1); auto.
        right; replace p2 with p1; omega.
      + split; auto; apply pow2_ge1.
      + constructor 2.
        apply lex_bar_br_1 with (l1 := 1) in H5; try omega.
        eq goal with H5; f_equal.
        - f_equal; simpl; omega.
        - rewrite <- (iter_plus f 1); f_equal; simpl.
          generalize (pow2_ge1 p2); omega.
  Qed.

  Let pre p l x y := x = f↑(p-1) x0 
                  /\ y = f↑(l+p-1) x0
                  /\ 1 <= l <= p
                  /\ exists k, p = pow2 k.

  Let post p l k := exists q, p <= pow2 q 
                           /\ 1 <= k <= pow2 q 
                           /\ f↑(pow2 q - 1) x0 = f↑(k+pow2 q - 1) x0
                           /\ forall l', 1 <= l' 
                                      -> f↑(pow2 q - 1) x0 = f↑(l'+pow2 q - 1) x0 
                                      -> p = pow2 q /\ (l' < l \/ k <= l') \/ p < pow2 q /\ k <= l'. 
 
  Let loop : forall p l x y (Hb : bar_br p l x y) (Hp : pre p l x y), { k | post p l k }.
  Proof.
    refine (fix loop p l x y Hb Hp := match x =? y with 
      | left E  => exist _ l _
      | right C => match eq_nat_dec p l with
                     | left E'   => match loop (2*p) 1 y (f y) _ _ with exist _ k Hk => exist _ k _ end 
                     | right C'  => match loop p (1+l) x (f y) _ _ with exist _ k Hk => exist _ k _ end 
                   end
    end); trivial.
    
    1,2,5: cycle 1.
    
    1,2: inversion Hb; trivial; [ destruct C; trivial | exfalso; omega ].
    
    1,2,4: cycle 1.
    
    * destruct Hp as (H1 & H2 & H3 & q & Hq).
      repeat split; try omega.
      rewrite H2; f_equal; omega.
      rewrite H2.
      change (f (f↑(l+p-1) x0)) with (f↑(1+(l+p-1)) x0).
      f_equal; omega.
      exists (S q); simpl; omega.
      
    * destruct Hp as (H1 & H2 & H3 & q & Hq).
      repeat split; auto; try omega.
      rewrite H2.
      change (f (f↑(l+p-1) x0)) with (f↑(1+(l+p-1)) x0).
      f_equal; omega.
      exists q; auto.
      
    * destruct Hp as (H1 & H2 & H3 & q & Hq).
      exists q; repeat split; try omega.
      rewrite <- Hq, <- H1, E; auto.
      intros l' _ _; left; omega.

    * destruct Hk as (q & H1 & H2 & H3 & H4).
      exists q; repeat split; auto; try omega.
      intros l' Hl' H5; specialize (H4 _ Hl' H5).
      destruct Hp as (_ & _ & Hp & _); omega.

    * destruct Hk as (q & H1 & H2 & H3 & H4).
      exists q; repeat split; auto; try omega.
      intros l' Hl' H5.
      specialize (H4 _ Hl' H5). 
      destruct H4 as [ (H4 & [ H6 | H6 ]) | (H4 & H6) ]; try omega.
      destruct (eq_nat_dec l l') as [ H7 | ]; try omega.
      destruct Hp as (G1 & G2 & _).
      subst p l' x y; destruct C; trivial.
  Qed.
  
  Let pre_bar p l x y : pre p l x y -> bar_br p l x y.
  Proof.
    intros (H1 & H2 & H3 & k & Hk).
    destruct brent_cyclicity with (1 := Hx0) (p := k) as (l' & q & H4 & H5 & H6).
    subst x y p; apply lex_bar_br with (3 := H5); auto.
    rewrite H6; constructor 1.
  Qed.

  (* We deduce the full specification of Brent's algorithm which computes the period *)

  Definition brent_bin : { μ |   0 < μ 
                         /\ (exists λ, f↑λ x0 = f↑(λ+μ) x0) 
                         /\ forall i j, i < j -> f↑i x0 = f↑j x0 -> μ div (j-i) }.
  Proof. 
    assert (pre 1 1 x0 (f x0)) as H.
      repeat split; auto.
      exists 0; auto.
    destruct (loop (pre_bar H) H) as (m & Hm).
    exists m.
    destruct Hm as (q & H1 & H2 & H3 & H4).
    split; [ omega | ].
    assert (forall l', 1 <= l' -> f ↑ (pow2 q - 1) x0 = f ↑ (l' + (pow2 q - 1)) x0 -> m <= l') as H0.
      intros l' G1 G2.
      replace (l' + (pow2 q - 1)) with (l' + pow2 q - 1) in G2 by omega.
      specialize (H4 _ G1 G2); omega.
    clear H4; rename H0 into H4.
    replace (m + pow2 q - 1) with (m + (pow2 q - 1)) in H3 by omega.
    revert H1 H2 H3 H4.
    generalize (pow2 q -1).
    intros l _ (Hm & _) H3 H4; clear q.
    split. 
    exists l; rewrite H3; f_equal; omega.
    intros i j H5 H6.
    destruct (eucl_dev _ Hm (j-i)) as [ q r G1 G2 ].
    destruct (le_lt_dec 1 r).
    2: exists q; omega.
    replace j with (r+q*m+i) in H6 by omega.
    assert (f↑l x0 = f↑(r+(q*m+l)) x0) as G3.
      rewrite plus_assoc.
      apply iter_xchg with (3 := H6) (4 := H3); omega.
    rewrite <- iter_loop_gen in G3; auto.
    apply H4 in G3; omega.
  Qed.

End Brent.

Check brent_bin.
Print Assumptions brent_bin.
Recursive Extraction brent_bin.
