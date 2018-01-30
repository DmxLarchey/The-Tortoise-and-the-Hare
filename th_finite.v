(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List.

Require Import utils tortoise_hare php.

Set Implicit Arguments.

Fixpoint list_n n := 
  match n with 
    | 0 => nil
    | S n => n::list_n n
  end.
  
Fact list_n_length n : length (list_n n) = n.
Proof. induction n; simpl; auto. Qed.
  
Fact list_n_spec n i : In i (list_n n) <-> i < n.
Proof.
  revert i; induction n as [ | n IHn ]; simpl; intros i.
  omega.
  rewrite IHn; omega.
Qed.

Fact list_n_map_inv X (f : nat -> X) n l x r :
    map f (list_n n) = l++x::r -> x = f (length r).
Proof.
  revert l x r.
  induction n as [ | n IHn ]; intros l x r H.
  destruct l; discriminate.
  destruct l as [ | y l ]; simpl in H; inversion H; subst.
  rewrite map_length, list_n_length; auto.
  apply IHn with (1 := H2).
Qed.

Section tortoise_hare_finite_domain.

  Variables (X : Type) (HX : exists l : list X, forall x, In x l)
            (eqdec : forall x y : X, { x = y } + { x <> y })
            (f : X -> X) (x0 : X).
            
  Definition th_finite : { τ | 0 < τ /\ f↑τ x0 = f↑(2*τ) x0 }.
  Proof.
    apply tortoise_hare_tail; trivial.
    destruct HX as (l & Hl).
    do 3 apply cyclicity_prop.
    destruct finite_pigeon_hole with (l := l) (m := map (fun n => iter f n x0) (list_n (S (length l))))
      as (x & aa & bb & cc & Hx) .
    rewrite map_length, list_n_length; auto.
    intros ? ?; apply Hl.
    exists (length (bb++x::cc)), (length cc); split.
    rewrite app_length; simpl; omega.
    transitivity x; auto.
    symmetry; revert Hx; apply list_n_map_inv.
    apply list_n_map_inv with (f := fun n => iter f n x0) (n := S(length l)) (l := aa++x::bb) (r := cc).
    rewrite Hx, app_ass; auto.
  Defined.
  
End tortoise_hare_finite_domain.

Check th_finite.
Print Assumptions th_finite.
Recursive Extraction th_finite.