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

Section Brent_cyclicity.

  Variables (X : Type) (f : X -> X) (x0 : X) (Hx0 : exists τ, 0 < τ /\ f↑τ x0 = f↑(2*τ) x0).
  
  (* This is another cyclicity condition *)
  
  Fact brent_cyclicity p : exists l q, p < q /\ 1 <= l <= pow2 q /\ f↑(pow2 q - 1) x0 = f↑(l+pow2 q - 1) x0.
  Proof.
    destruct Hx0 as (m & H1 & H2).
    destruct (pow2_inter H1) as (q & Hq).
    assert (m < pow2 (S (p+q))) as Hm.
    { apply lt_le_trans with (pow2 (S q)).
      omega.
      rewrite <- pow2_mono; omega. }
    exists m, (S (p+q)).
    repeat split; try omega.
    revert Hm; generalize (pow2 (S (p+q))); intros n Hn.
    replace (n-1) with ((n-1-m)+m) by omega.
    replace (m+n-1) with ((n-1-m)+2*m) by omega.
    do 2 rewrite iter_plus; f_equal; auto.
  Qed.
  
End Brent_cyclicity.