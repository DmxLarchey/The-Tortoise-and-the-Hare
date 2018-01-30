(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Euclid Omega Relations.

Require Import utils.

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

  Variable (f : X -> X) (x0 : X) 
           (Hx0 : exists τ, 0 < τ /\ f↑τ x0 = f↑(2*τ) x0).

  Let Hx0' p : exists l q, p < q /\ 1 <= l <= pow2 q /\ f↑(pow2 q - 1) x0 = f↑(l+pow2 q - 1) x0.
  Proof.
    destruct Hx0 as (m & H1 & H2).
    destruct (pow2_inter H1) as (q & Hq).
    assert (m < pow2 (S (p+q))) as Hm.
      apply lt_le_trans with (pow2 (S q)).
      omega.
      rewrite <- pow2_mono; omega.
    exists m, (S (p+q)).
    split.
    omega.
    split.
    generalize (pow2_ge1 q); omega.
    revert Hm; generalize (pow2 (S (p+q))); intros n Hn.
    replace (n-1) with ((n-1-m)+m) by omega.
    replace (m+n-1) with ((n-1-m)+2*m) by omega.
    do 2 rewrite iter_plus; f_equal; auto.
  Qed.
  
  Inductive bar_br l p m x y :  Prop :=
    | in_bar_br_0 :           x = y                        
                           -> bar_br l p m x y 

    | in_bar_br_1 :           m = 0 
                           -> bar_br 1 (S p) p y (f y) 
                           -> bar_br l    p  m x    y

    | in_bar_br_2 : forall n, m = S n
                           -> bar_br (S l) (S p) n x (f y)      
                           -> bar_br    l     p  m x    y.
                                     
  Local Fact bar_br_1_inv l p m x y : x <> y -> m = 0 -> bar_br l p m x y -> bar_br 1 (S p) p y (f y).
  Proof.
    intros H1 H2 H3.
    revert H3 H1 H2.
    intros [ H3 | H H3 | n H H3 ] H1 H2.
    destruct (H1 H3).
    exact H3.
    subst m; discriminate.
  Defined.
  
  Local Fact bar_br_2_inv l p m x y n : x <> y -> m = S n -> bar_br l p m x y -> bar_br (S l) (S p) n x (f y).
  Proof.
    intros H1 H2 H3; revert H3 n H1 H2.
    intros [ H3 | H H3 | n H H3 ] k H1 H2.
    destruct (H1 H3).
    subst m; discriminate.
    subst m.
    apply f_equal with (f := pred) in H2.
    simpl in H2.
    subst n.
    exact H3.
  Defined.

  Local Fact lex_bar_br_1 q l1 l2 :
         l1 <= l2
      -> l2 <= pow2 q
      -> bar_br l2 (pow2 q+l2-1) (pow2 q-l2) (f↑(pow2 q-1) x0) (f↑(l2+pow2 q-1) x0)
      -> bar_br l1 (pow2 q+l1-1) (pow2 q-l1) (f↑(pow2 q-1) x0) (f↑(l1+pow2 q-1) x0).
  Proof.
    induction 1 as [ | l2 H2 IH2 ]; intros H4 H5; auto.
    apply IH2; try omega.
    case_eq (pow2 q - l2).
    intros; exfalso; omega.
    
    intros n Hn; constructor 3 with n; trivial. 
    eq goal with H5.
    f_equal; try omega.
    rewrite <- (iter_plus f 1); f_equal; omega.
  Qed.

  Local Fact lex_bar_br q1 l1 q2 l2 : 
         (q1 < q2 \/ q1 = q2 /\ l1 <= l2)
      -> 1 <= l1 <= pow2 q1
      -> 1 <= l2 <= pow2 q2
      -> bar_br l2 (pow2 q2+l2-1) (pow2 q2-l2) (f↑(pow2 q2-1) x0) (f↑(l2+pow2 q2-1) x0)
      -> bar_br l1 (pow2 q1+l1-1) (pow2 q1-l1) (f↑(pow2 q1-1) x0) (f↑(l1+pow2 q1-1) x0).
   Proof.
    intros H1 H3 H4.
    assert (q1 <= q2) as H.
      omega.
    revert l1 l2 H1 H3 H4.
    induction H as [ | q2 H IH ].

    intros l1 l2 [ H1 | (H1 & H2) ] (H3 & _) (_ & H4).
    exfalso; omega.
    apply lex_bar_br_1; auto.

    intros l1 l2 _ H3 H4 H5.
    apply IH with (l2 := pow2 q2); auto.
    destruct (le_lt_dec q2 q1).
    right; replace q2 with q1; omega.
    left; auto.
    split; auto.
    apply pow2_ge1.
    rewrite minus_diag.
    constructor 2; trivial.
    apply lex_bar_br_1 with (l1 := 1) in H5; try omega.
    eq goal with H5; f_equal; try (simpl; omega).
    f_equal; generalize (pow2_ge1 q2); simpl; omega.
    f_equal; simpl; omega.
    rewrite <- (iter_plus f 1); f_equal; simpl. 
    generalize (pow2_ge1 q2); omega.
  Qed.

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
 
  Let pre_bar l ppl pml x y : pre l ppl pml x y -> bar_br l ppl pml x y.
  Proof.
    intros (q & H1 & H2 & H3 & H4 & H5).
    destruct (Hx0' q) as (l' & q' & H7 & H8 & H9).
    subst x y ppl pml.
    apply in_bar_br_0 with (l := l') (p := pow2 q'+l'-1) (m := pow2 q'-l') in H9.
    revert H9; apply lex_bar_br; omega.
  Qed.

  (* This is a bit complicated because we need equations m = 0 and m = S n
     to build the termination certificate *)

  Let loop : forall l p m x y (Hb : bar_br l p m x y) (Hp : pre l p m x y), { k | post l p k }.
  Proof.
    refine (fix loop l p m x y Hb Hp := match x =? y with 
      | left E  => exist _ l _
      | right C => match m as m0 return (m = m0 -> { k | post l p k })
                   with 
                     | 0   => fun Hm => match loop    1  (S p) p y (f y) _ _ with exist _ k Hk => exist _ k _ end
                     | S n => fun Hm => match loop (S l) (S p) n x (f y) _ _ with exist _ k Hk => exist _ k _ end
                   end eq_refl
    end); trivial.

    destruct Hp as (q & H1 & H2 & H3 & H4 & H5).
    exists q; repeat split; try omega.
    rewrite <- H2, <- H1; auto.
    intros l' _ _; left; omega.
    
    (* The first termination certificate *)
    exact (bar_br_1_inv C Hm Hb). 

    destruct Hp as (q & H1 & H2 & H3 & H4 & H5).
    exists (S q); repeat split; try (simpl; omega).
    rewrite H2; f_equal; simpl; omega.
    rewrite H2.
    change (f (f↑(l+pow2 q-1) x0)) with (f↑(1+(l+pow2 q-1)) x0).
    f_equal; simpl; omega.

    destruct Hk as (q' & H1 & H2 & H3 & H4).
    exists q'; repeat split; auto; try omega.
    intros l' Hl' H5; specialize (H4 _ Hl' H5).
    destruct Hp as (q & _ & _ & Hp & _); omega.

    (* The second termination certificate *)
    exact (bar_br_2_inv C Hm Hb).

    destruct Hp as (q & H1 & H2 & H3 & H4 & H5).
    exists q; repeat split; auto; try omega.
    rewrite H2.
    change (f (f↑(l+pow2 q-1) x0)) with (f↑(1+(l+pow2 q-1)) x0).
    f_equal; simpl; omega.

    destruct Hk as (q' & H1 & H2 & H3 & H4).
    exists q'; repeat split; auto; try omega.
    intros l' Hl' H5.
    specialize (H4 _ Hl' H5). 
    destruct H4 as [ (H4 & [ H6 | H6 ]) | (H4 & H6) ]; try omega.
    destruct (eq_nat_dec l l') as [ H7 | ]; try omega.
    destruct Hp as (q & G1 & G2 & G3 & G4 & G5).
    assert (q = q') as H8.
      apply pow2_inj; omega.
    subst q' l' x y p; destruct C; trivial.
  Qed.

  (* We deduce the full specification of Brent's algorithm which computes the period *)

  Definition brent_una : { μ |   0 < μ 
                         /\ (exists λ, f↑λ x0 = f↑(λ+μ) x0) 
                         /\ forall i j, i < j -> f↑i x0 = f↑j x0 -> μ div (j-i) }.
  Proof. 
    assert (pre 1 1 0 x0 (f x0)) as H.
      exists 0; repeat split; auto.
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
  Defined.

End Brent.

Check brent_una.
Print Assumptions brent_una.
Extraction brent_una.
