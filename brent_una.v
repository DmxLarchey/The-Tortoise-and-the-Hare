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
    algorithm refined for unary nats. It extracts to
    the following OCaml code

    type nat = O | S of nat
    type sumbool = Left | Right

    let brent eqdec f x0 =
      let rec loop l p m x y =
        match eqdec x y with
          | Left -> l
          | Right -> (match m with
            | O   -> loop (S O) (S p) p y (f y)
            | S n -> loop (S l) (S p) n x (f y))
    in loop (S O) (S O) O x0 (f x0)

*)

Section Brent.

  Variables (X : Type) (eqdec : forall x y : X, { x = y } + { x <> y }).
  
  Infix "=?" := eqdec (at level 70).

  Variable (f : X -> X) (x0 : X) (Hx0 : exists τ, 0 < τ /\ f↑τ x0 = f↑(2*τ) x0).

  Inductive bar_br l p : nat -> X -> X ->  Prop :=
    | in_bar_br_0 : forall m x,   bar_br    l    p      m  x    x 

    | in_bar_br_1 : forall x y,   bar_br    1 (S p)     p  y (f y) 
                             ->   bar_br    l    p      0  x    y

    | in_bar_br_2 : forall m x y, bar_br (S l) (S p)    m  x (f y)      
                             ->   bar_br    l     p  (S m) x    y.

  (* pre explains the meaning of p and l w.r.t. the conventional Brent algorithm
     which is OK for binary nats but not for unary nats

     - p is 2^q + l - 1   and      m is 2^q - l   
          for some 1 <= l <= 2^q

     the test l = 2^q is replaced with m = 0
   *)

  Let pre l p m x y := exists q,
                     x = f↑(pow2 q-1) x0 
                  /\ y = f↑(l+pow2 q-1) x0
                  /\ 1 <= l <= pow2 q
                  /\ p = pow2 q+l-1
                  /\ m = pow2 q-l.

  Let post l p k := exists q,  p <= pow2 q + l - 1 
                            /\ 1 <= k <= pow2 q 
                            /\ f↑(pow2 q - 1) x0 = f↑(k+pow2 q - 1) x0
                            /\ forall l', 1 <= l' 
                                       -> f↑(pow2 q - 1) x0 = f↑(l'+pow2 q - 1) x0 
                                       -> p = pow2 q + l - 1 /\ (l' < l \/ k <= l')
                                       \/ p < pow2 q + l - 1 /\ k <= l'. 

  (* This is a bit complicated because we need equations m = 0 and m = S n
     to build the termination certificate *)
     
  Let loop : forall l p m x y (Hb : bar_br l p m x y) (Hp : pre l p m x y), { k | post l p k }.
  Proof.
    refine (fix loop l p m x y Hb Hp := match x =? y with 
      | left E  => exist _ l _
      | right C => match m as m' return bar_br l p m' x y -> pre l p m' x y -> _ with 
                     | 0   => fun Hb' Hp' => match loop    1  (S p) p y (f y) _ _ with exist _ k Hk => exist _ k _ end
                     | S n => fun Hb' Hp' => match loop (S l) (S p) n x (f y) _ _ with exist _ k Hk => exist _ k _ end
                   end Hb Hp 
    end); trivial.
    1,2,5: cycle 1.

    (* The two termination certificates *)
    1,2: revert C; inversion Hb'; trivial; intros []; trivial.
    
    2-5: clear Hb Hp; rename Hb' into Hb; rename Hp' into Hp.
    1,2,4: cycle 1.
    
    (* Check the pre-conditions *)
    
    * destruct Hp as (q & H1 & H2 & H3 & H4 & H5).
      exists (S q); repeat split; try (simpl; omega).
      rewrite H2; f_equal; simpl; omega.
      rewrite H2.
      change (f (f↑(l+pow2 q-1) x0)) with (f↑(1+(l+pow2 q-1)) x0).
      f_equal; simpl; omega.
     
    * destruct Hp as (q & H1 & H2 & H3 & H4 & H5).
      exists q; repeat split; auto; try omega.
      rewrite H2.
      change (f (f↑(l+pow2 q-1) x0)) with (f↑(1+(l+pow2 q-1)) x0).
      f_equal; simpl; omega.
    
    (* Check the post-conditions *)
 
    * destruct Hp as (q & H1 & H2 & H3 & H4 & H5).
      exists q; repeat split; try omega.
      rewrite <- H2, <- H1; auto.
      intros l' _ _; left; omega.
    
    * destruct Hk as (q' & H1 & H2 & H3 & H4).
      exists q'; repeat split; auto; try omega.
      intros l' Hl' H5; specialize (H4 _ Hl' H5).
      destruct Hp as (? & _ & _ & ? & _); omega.

    * destruct Hk as (q' & H1 & H2 & H3 & H4).
      exists q'; repeat split; auto; try omega.
      intros l' Hl' H5.
      specialize (H4 _ Hl' H5). 
      destruct H4 as [ (H4 & [ H6 | H6 ]) | (H4 & H6) ]; try omega.
      destruct (eq_nat_dec l l') as [ H7 | ]; try omega.
      destruct Hp as (q & G1 & G2 & G3 & G4 & G5).
      assert (q = q') as H8 by (apply pow2_inj; omega).
      subst q' l' x y p; destruct C; trivial.
  Qed.
  
  (* Properties of the domain using the 3rd constructor *)
  
  Local Fact lex_bar_br_0 l p m x y n : 
         bar_br (n+l) (n+p)   m  x (f↑n y)
      -> bar_br    l     p (n+m) x      y.
  Proof.
    revert l p m x y.
    induction n as [ | n IHn ]; simpl; auto; intros l p m x y H.
    constructor 3; apply IHn.
    eq goal with H; f_equal; try omega.
    rewrite <- (iter_plus f _ 1), plus_comm; auto.
  Qed.

  Local Fact lex_bar_br_1 q l1 l2 :
         l1 <= l2 <= pow2 q
      -> bar_br l2 (pow2 q+l2-1) (pow2 q-l2) (f↑(pow2 q-1) x0) (f↑(l2+pow2 q-1) x0)
      -> bar_br l1 (pow2 q+l1-1) (pow2 q-l1) (f↑(pow2 q-1) x0) (f↑(l1+pow2 q-1) x0).
  Proof.
    intros H1 H2.
    replace (pow2 q-l1) with ((l2 - l1)+ (pow2 q-l2)) by omega.
    apply lex_bar_br_0.
    eq goal with H2; f_equal; try omega.
    rewrite <- iter_plus; f_equal; omega.
  Qed.

  Local Fact lex_bar_br q1 l1 q2 l2 : 
         (q1 < q2 \/ q1 = q2 /\ l1 <= l2)
      -> 1 <= l1 <= pow2 q1
      -> 1 <= l2 <= pow2 q2
      -> bar_br l2 (pow2 q2+l2-1) (pow2 q2-l2) (f↑(pow2 q2-1) x0) (f↑(l2+pow2 q2-1) x0)
      -> bar_br l1 (pow2 q1+l1-1) (pow2 q1-l1) (f↑(pow2 q1-1) x0) (f↑(l1+pow2 q1-1) x0).
   Proof.
    intros H1 H3 H4.
    assert (q1 <= q2) as H by omega.
    revert H l1 l2 H1 H3 H4.
    induction 1 as [ | q2 H IH ]; intros l1 l2.
    * intros [ H1 | (H1 & H2) ] (H3 & _) (_ & H4).
      + exfalso; omega.
      + apply lex_bar_br_1; auto.
    * intros _ H3 H4 H5.
      apply IH with (l2 := pow2 q2); auto.
      + destruct (le_lt_dec q2 q1); auto.
        right; replace q2 with q1; omega.
      + split; auto; apply pow2_ge1.
      + rewrite minus_diag.
        constructor 2.
        apply lex_bar_br_1 with (l1 := 1) in H5; try omega.
       eq goal with H5; f_equal; try (simpl; omega).
       - f_equal; generalize (pow2_ge1 q2); simpl; omega.
       - f_equal; simpl; omega.
       - rewrite <- (iter_plus f 1); f_equal; simpl. 
         generalize (pow2_ge1 q2); omega.
  Qed.
  
  Let pre_bar l ppl pml x y : pre l ppl pml x y -> bar_br l ppl pml x y.
  Proof.
    intros (q & H1 & H2 & H3 & H4 & H5).
    destruct brent_cyclicity with (1 := Hx0) (p := q) as (l' & q' & H7 & H8 & H9).
    rewrite H1, H2, H4, H5.
    apply lex_bar_br with (3 := H8); auto.
    rewrite H9; constructor.
  Qed.

  (* We deduce the full specification of Brent's algorithm which computes the period *)

  Definition brent_una : { μ |   0 < μ 
                         /\ (exists λ, f↑λ x0 = f↑(λ+μ) x0) 
                         /\ forall i j, i < j -> f↑i x0 = f↑j x0 -> μ div (j-i) }.
  Proof. 
    assert (pre 1 1 0 x0 (f x0)) as H.
    { exists 0; repeat split; auto. }
    destruct (loop (pre_bar H) H) as (m & Hm).
    exists m.
    destruct Hm as (q & H1 & H2 & H3 & H4).
    split; try omega.
    assert (forall l', 1 <= l' -> f ↑ (pow2 q - 1) x0 = f ↑ (l' + (pow2 q - 1)) x0 -> m <= l') as H0.
    { intros l' G1 G2.
      replace (l' + (pow2 q - 1)) with (l' + pow2 q - 1) in G2 by omega.
      specialize (H4 _ G1 G2); omega. }
    clear H4; rename H0 into H4.
    replace (m + pow2 q - 1) with (m + (pow2 q - 1)) in H3 by omega.
    revert H1 H2 H3 H4.
    generalize (pow2 q -1).
    intros l _ (Hm & _) H3 H4; clear q.
    split. 
    * exists l; rewrite H3; f_equal; omega.
    * intros i j H5 H6.
      destruct (eucl_dev _ Hm (j-i)) as [ q r G1 G2 ].
      destruct (le_lt_dec 1 r); [ | exists q; omega ].
      replace j with (r+q*m+i) in H6 by omega.
      assert (f↑l x0 = f↑(r+(q*m+l)) x0) as G3.
      { rewrite plus_assoc.
        apply iter_xchg with (3 := H6) (4 := H3); omega. }
      rewrite <- iter_loop_gen in G3; auto.
      apply H4 in G3; omega.
  Qed.

End Brent.

Check brent_una.
Print Assumptions brent_una.
Recursive Extraction brent_una.
