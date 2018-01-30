(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Euclid Omega.

Set Implicit Arguments.

Tactic Notation "eq" "goal" "with" hyp(H) := 
  match goal with 
    |- ?b => match type of H with ?t => replace b with t; auto end 
  end.
  
Section nat_rev_ind.

  (** A reverse recursion principle *)

  Variables (P : nat -> Prop)
            (HP : forall n, P (S n) -> P n).

  Theorem nat_rev_ind x y : x <= y -> P y -> P x.
  Proof. induction 1; auto. Qed.

End nat_rev_ind.

Section le_rect.

  Variables (n : nat) (P : nat -> Type)
            (H0 : P n) (H1 : forall m : nat, n <= m -> P m -> P (S m)).

  Theorem le_rect m : n <= m -> P m.
  Proof.
    intros H.
    replace m with ((m-n)+n) by omega.
    generalize (m-n); clear H m.
    intros m.
    induction m as [ | m IHm ]; auto.
    simpl; apply H1; auto; omega.
  Qed.

End le_rect.

Definition least_upto X (R : X -> X -> Prop) (P : X -> Prop) := { n | P n /\ forall k, P k -> R n k }.

Section nat_utils.

  Definition least_le := least_upto le.
  
  Definition nat_divides k p := exists q, p = q*k.
  
  Definition least_div := least_upto nat_divides.  
  
  Definition least_nat_pair (P : nat -> nat -> Prop) := 
     { n : nat & { m | P n m /\ forall n' m', P n' m' -> n <= n' /\ m <= m' } }.

  Fact nat_Sn_P1_eq n : S n = n + 1.
  Proof. omega. Qed.
  
  Fact nat_2Sn_2nP2_eq n : 2*(S n) = 2*n+2.
  Proof. simpl; omega. Qed.
  
  Definition nat_archi a b : 0 < a -> { k | 0 < k /\ k*a >= b }.
  Proof.
    exists (1+b).
    split.
    omega.
    replace b with (b * 1) at 2 by omega.
    apply mult_le_compat; omega.
  Qed.

  Implicit Type f : nat -> nat.

  Fact nat_sinc_mono f : (forall n, f n < f (S n)) -> forall i j, i <= j -> f i <= f j.
  Proof.
    intros H.
    induction 1; auto.
    apply le_trans with (2 := lt_le_weak _ _ (H _)); auto. 
  Qed.

  Fact nat_sinc f : (forall n, f n < f (S n)) -> forall i j, i < j -> f i < f j.
  Proof.
    intros H ? ? ?.
    apply le_trans with (1 := H _), nat_sinc_mono; auto.
  Qed.
    
  Fact nat_inter_value f : 
           (forall n, f n < f (S n)) 
        -> forall i, { n | f n <= i < f (S n) } + { i < f 0 }.
  Proof.
    intros Hf i.
    destruct (le_lt_dec (f 0) i) as [ Hi | ].
    2: right; auto.
    left.
    induction Hi as [ | j Hj IHj ] using le_rect.
    exists 0; split; auto.
    destruct IHj as (n & Hn).
    destruct (le_lt_dec (f (S n)) (S j)) as [ H | H ].
    exists (S n); generalize (Hf (S n)); split; omega.
    exists n; split; omega.
  Qed.

End nat_utils.

Section pow2.

  Fixpoint pow2 n :=
    match n with 
      | 0   => 1 
      | S n => 2*pow2 n
    end.

  Fact pow2_ge1 n : 1 <= pow2 n.
  Proof. induction n; simpl; omega. Qed.

  Fact pow2_sinc n : pow2 n < pow2 (S n).
  Proof. generalize (pow2_ge1 n); simpl; omega. Qed.

  Fact pow2_inter n : 1 <= n -> { k | pow2 k <= n < pow2 (S k) }.
  Proof.
    intros H.
    destruct (nat_inter_value _ pow2_sinc n) as [ | C ]; auto.
    exfalso; simpl in C; omega.
  Qed.

  Definition log2 (n : nat) : nat.
  Proof. 
    refine (match n with 
      | 0   => 0
      | S n => proj1_sig (@pow2_inter (S n) _)
    end).
    apply le_n_S, le_0_n.
  Defined.

  Fact log2_spec n : 0 < n -> pow2 (log2 n) <= n < pow2 (S (log2 n)).
  Proof.
    intros H.
    destruct n.
    omega.
    apply (proj2_sig (@pow2_inter (S n) _)).
  Qed.

  Fact pow2_mono n m : n <= m <-> pow2 n <= pow2 m.
  Proof.
    split.
    apply nat_sinc_mono, pow2_sinc.
    intros H.
    destruct (le_lt_dec n m) as [ | H1 ]; auto.
    apply nat_sinc with (1 := pow2_sinc) in H1.
    omega.
  Qed.

  Fact pow2_inj n m : pow2 n = pow2 m -> n = m.
  Proof.
    intro; apply le_antisym; rewrite pow2_mono; omega.
  Qed.

End pow2.  

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
  
Tactic Notation "eq" "iter" :=
  match goal with 
    | |- _      = ?f↑_ _ => rew iter f
    | |- ?f↑_ _ = _      => rew iter f
    | |- _      = ?f _   => rew iter f
    | |- ?f _   = _      => rew iter f
  end;
  try (f_equal; simpl; omega).

Tactic Notation "finish" "with" hyp(H) := 
  eq goal with H; f_equal; eq iter.

Section iter_props.

  Variables (X : Type) (f : X -> X).
  
  Section iter_with_loop.

    (** There is a loop of length a containing f↑n x *)
 
    Variable (n a : nat) (x : X) 
             (Hx : f↑n x = f↑(a+n) x).
  
    Fact iter_loop_gen i j : f↑(i+n) x = f↑(i+(j*a+n)) x.
    Proof.
      do 2 rewrite iter_plus; f_equal.
      induction j as [ | j ]; auto.
      rewrite Hx, iter_plus, IHj.
      eq iter.
    Qed.
    
    (* The tortoise meets the hare *)

    Fact iter_tmh : 0 < a -> exists k, 0 < k /\ f↑k x = f↑(2*k) x.
    Proof.
      intros Ha.
      exists ((1+n)*a); split.
      simpl; generalize (n*a); intro; omega.
      assert (n <= (1+n)*a).
        replace n with (n*1) at 1 by omega.
        apply mult_le_compat; omega.
      replace ((1+n)*a) with ((1+n)*a-n+n) at 1 by omega.
      replace (2*((1+n)*a)) with ((1+n)*a-n+((1+n)*a+n)) by omega.
      apply iter_loop_gen; trivial.
    Qed.
    
  End iter_with_loop.
  
  Fact iter_double_eq x k : f↑k x = f↑(2*k) x -> forall i j, 0 < j -> f↑(i+k) x = f↑(i+j*k) x.
  Proof.
    intros H i j Hj.
    rewrite iter_loop_gen with (a := k) (j := (j-1)).
    f_equal.
    replace j with (j-1+1) at 2 by omega.
    rewrite Nat.mul_add_distr_r; omega.
    finish with H.
  Qed.
  
  Lemma iter_tmh_cycle_equiv x :
         (exists τ, 0 < τ /\ f↑τ x = f↑(2*τ) x) 
     <-> (exists λ μ, 0 < μ /\ f↑λ x = f↑(λ+μ) x).
  Proof.
    split.
    * intros (k & H1 & H2).
      exists k, k; split; auto.
      finish with H2.
    * intros (n & a & H1 & H2).
      apply iter_tmh with n a; auto.
      finish with H2.
  Qed.
  
  Proposition cyclicity_prop x :
           ( (exists i j, i <> j /\ f↑i x = f↑j x) -> (exists λ μ, 0 < μ /\ f↑λ x = f↑(λ+μ) x) )
        /\ ( (exists λ μ, 0 < μ /\ f↑λ x = f↑(λ+μ) x) -> (exists λ μ, 0 < μ /\ forall i j, f↑(i+λ) x = f↑(i+λ+j*μ) x) )
        /\ ( (exists λ μ, 0 < μ /\ forall i j, f↑(i+λ) x = f↑(i+λ+j*μ) x) -> (exists τ, 0 < τ /\ f↑τ x = f↑(2*τ) x) )
        /\ ( (exists τ, 0 < τ /\ f↑τ x = f↑(2*τ) x) -> (exists i j, i <> j /\ f↑i x = f↑j x) ).
  Proof.
    repeat split.
    
    intros (i & j & H1 & H2).
    destruct (le_lt_dec i j); 
      [ exists i, (j - i) 
      | symmetry in H2; exists j, (i - j) ]; 
      (split; [ omega | ]; finish with H2).

    intros (n & a & H1 & H2); exists n, a; split; auto.
    intros i j; rewrite <- plus_assoc, (plus_comm n); apply iter_loop_gen.
    finish with H2.
    
    intros (n & a & H1 & H2).
    apply iter_tmh_cycle_equiv.
    exists n, a; split; auto.
    specialize (H2 0 1); simpl in H2.
    finish with H2.
    
    intros (t & H1 & H2).
    exists t, (2*t); split; auto; omega.
  Qed.

  Fact iter_factor x a b n m :
          0 < n 
       -> 0 < m
       -> f↑a x = f↑(n+a) x
       -> f↑b x = f↑(m+b) x
       -> exists k, f↑b x = f↑(k+a) x.
  Proof.
    intros H1 H2 H3 H4.
    destruct (nat_archi a H2) as (j & Hj).
    exists (j*m+b-a).
    replace (j*m+b-a+a) with (j*m+b) by omega.
    apply iter_loop_gen with (i := 0); auto.
  Qed.
  
  Fact iter_xchg x a b n m :
          0 < n 
       -> 0 < m 
       -> f↑a x = f↑(n+a) x
       -> f↑b x = f↑(m+b) x
       -> f↑b x = f↑(n+b) x.
  Proof.
    intros Hn Hm Ha Hb.
    destruct (@nat_archi m a) as (k & Hk); auto.
    generalize (@iter_loop_gen _ _ _ Hb); intros H1.
    rewrite (H1 n k).
    specialize (H1 0); simpl in H1.
    rewrite (H1 k).
    replace (k*m+b) with (k*m+b-a+a) at 1 by omega.
    replace (n+(k*m+b)) with (k*m+b-a+(n+a)) by omega.
    do 2 rewrite iter_plus with (a := k*m+b-a).
    f_equal; auto.
  Qed.
  
End iter_props.

