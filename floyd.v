(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Euclid Omega.

Require Import utils.

Set Implicit Arguments.

Local Infix "div" := (nat_divides) (at level 70). 

Section Floyd_cycle_finding_algo.

  Variables (X : Type) (eqdec : forall x y : X, { x = y } + { x <> y }).
  
  Variables (f : X -> X) (x0 : X) (Hx0 : exists τ, 0 < τ /\ f↑τ x0 = f↑(2*τ) x0).
  
  (** the sequence starting at x leads to a cycle *)
                
  Let ends_in_cycle x := exists λ μ, 0 < μ /\ f↑λ x = f↑(λ+μ) x.
  
  (** the tortoise and the hare will meet *)
    
  Let tortoise_meets_hare x := exists τ, 0 < τ /\ f↑τ x = f↑(2*τ) x.
  
  (** x is a loop of f *)
  
  Definition iter_in_cycle x := exists k, 0 < k /\ x = f↑k x.

  (** k is a period of the loop when starting from x *)

  Definition iter_is_period x k := 0 < k /\ exists l, f↑l x = f↑(k+l) x.
  
  Ltac iter_in_cycle_tac :=
    match goal with 
      | H: f↑?n ?x = f↑(?a+?n) ?x |- iter_in_cycle (f↑?n ?x) => exists a; split; auto; finish with H 
      | H: ?x = f↑?a ?x           |- iter_in_cycle ?x        => exists a; split; auto; finish with H
      end.
      
  Ltac iter_is_period_tac :=
    match goal with 
      | H: f↑?n ?x = f↑(?a+?n) ?x   |- iter_is_period ?x ?a => split; auto; try omega; exists n; finish with H
      | H: f↑?n ?x = f↑?a (f↑?n ?x) |- iter_is_period ?x ?a => split; auto; try omega; exists n; finish with H
    end.
    
  Hint Extern 4 (iter_in_cycle _)    => iter_in_cycle_tac.
  Hint Extern 4 (iter_is_period _ _) => iter_is_period_tac.
  
  Fact iter_in_cycle_period x l k : 
         iter_in_cycle (f↑l x) 
      -> iter_is_period x k
      -> f↑l x = f↑(l+k) x.  
  Proof.
    intros (p & Hp1 & Hp2) (Hk1 & m & Hm).
    rewrite <- iter_plus in Hp2.
    rewrite plus_comm; revert Hm Hp2; apply iter_xchg; auto.
  Qed.

  Section compute_meeting_point.

    Inductive bar_th x y : Prop :=
      | in_bar_th_0 : x = y                  -> bar_th x y 
      | in_bar_th_1 : bar_th (f x) (f (f y)) -> bar_th x y.

    Let bar_th_meet : forall x y, bar_th x y -> { c | exists k, c = f↑k x /\ c = f↑(2*k) y }.
    Proof.
      refine(fix loop x y H {struct H} := 
           match eqdec x y with
               | left E  => exist _ x _
               | right C => match loop (f x) (f (f y)) _ with
                              | exist _ c Hc => exist _ c _
                            end
           end).
      * exists 0; subst; simpl; split; trivial.
      * destruct H; auto; contradict C; trivial.
      * destruct Hc as (k & H1 & H2).
        exists (S k).
        rewrite H1 at 1; rewrite H2.
        split; eq iter.
    Qed.

    Let bar_th_fx0_ffx0 : bar_th (f x0) (f (f x0)).
    Proof.
      destruct Hx0 as (k & H3 & H4).
      apply in_bar_th_0 in H4.
      revert k H3 H4; apply nat_rev_ind.
      intros ? H; apply in_bar_th_1; finish with H.
    Qed.

    Definition floyd_meeting_pt : { c | exists τ, 0 < τ /\ c = f↑τ x0 /\ c = f↑(2*τ) x0 }.
    Proof.
      refine (match bar_th_meet bar_th_fx0_ffx0 with
                | exist _ c Hc => exist _ c _
              end).
      destruct Hc as (k & H1 & H2).
      exists (S k); split; try omega.
      rewrite H1 at 1; rewrite H2.
      split; eq iter.
    Defined.
    
  End compute_meeting_point.
  
  Section compute_index.
  
    Inductive bar_in i x y : Prop :=
      | in_bar_in_0 : x = y                    -> bar_in i x y
      | in_bar_in_1 : bar_in (S i) (f x) (f y) -> bar_in i x y.
      
    Let iter_bar_in n x y : bar_in n (f↑n x) (f↑n y) -> bar_in 0 x y.
    Proof.
      generalize n (le_O_n n); apply nat_rev_ind.
      constructor 2; auto.
    Qed.
      
    Let bar_in_inv : forall i x y, bar_in i x y -> least_le (fun n => i <= n /\ f↑(n-i) x = f↑(n-i) y).
    Proof.
      refine (fix loop i x y H { struct H } := 
            match eqdec x y with
              | left  E => exist _ i _
              | right N => match loop (S i) (f x) (f y) _ with
                             | exist _ n Hn => exist _ n _
                           end
            end).
      * split; subst; auto.
        intros ? []; auto.
      * destruct H; auto; destruct N; auto.
      * destruct Hn as ((H1 & H2) & H3); split.
        - split; try omega; finish with H2.
        - intros k (H4 & H5).
          destruct (eq_nat_dec i k).
          + subst; destruct N.
            repeat rewrite minus_diag in H5; auto.
          + apply H3.
            split; try omega.
            finish with H5.
    Qed.
 
    Variable (c : X) (Hc : exists τ, 0 < τ /\ c = f↑τ x0 /\ c = f↑(2*τ) x0).
    
    Let bar_in_0_x0_c : bar_in 0 x0 c.
    Proof.
      destruct Hc as (n & _ & Hn1 & Hn2).
      rewrite Hn1.
      apply iter_bar_in with n, in_bar_in_0.
      rewrite <- Hn1 at 1; finish with Hn2.
    Qed.
    
    Definition floyd_index : least_le (fun l => iter_in_cycle (f↑l x0)). 
    Proof.
      refine (match bar_in_inv bar_in_0_x0_c with
                | exist _ n Hn => exist _ n _
              end).
      destruct Hn as ((H0 & H1) & H2).
      destruct Hc as (m & H3 & H4 & H5).
      repeat rewrite <- minus_n_O in H1.
      split.
      
      exists m; split; auto.
      rewrite H1, <- iter_plus, plus_comm, iter_plus; f_equal.
      rewrite H4 at 2; finish with H5.
    
      intros k (p & H6 & H7).
      apply H2.
      split; try omega.
      repeat rewrite <- minus_n_O.
      rewrite <- iter_plus in H7.
      generalize (iter_loop_gen _ _ _ _ H7 0); clear H7; simpl; intros H7.
      rewrite H4 in H5; replace (2*m) with (m+m) in H5 by omega.
      generalize (iter_loop_gen _ _ _ _ H5 0); clear H5; simpl; intros H5.
      rewrite H4.
      rewrite H7 with (j := m).
      rewrite H5 with (j := p-1), <- iter_plus.
      f_equal.
      replace p with (p-1+1) at 1 by omega.
      rewrite Nat.mul_add_distr_l, mult_comm; omega.
    Defined.
    
  End compute_index.
  
  Section compute_period.
  
    Variable (c : X) (Hx : exists k, 0 < k /\ c = f↑k c).

    Inductive bar_pe i y : Prop :=
      | in_bar_pe_0 : c = y              -> bar_pe i y
      | in_bar_pe_1 : bar_pe (S i) (f y) -> bar_pe i y.
      
    Let iter_bar_pe n y : 0 < n -> bar_pe n (f↑n y) -> bar_pe 1 (f y).
    Proof.
      generalize n; apply nat_rev_ind.
      constructor 2; auto.
    Qed.
  
    Let bar_pe_inv : forall i y, bar_pe i y -> least_le (fun n => i <= n /\ c = f↑(n-i) y). 
    Proof.
      refine (fix loop i y H { struct H } :=
            match eqdec c y with
              | left  E => exist _ i _
              | right N => match loop (S i) (f y) _ with
                             | exist _ n Hn => exist _ n _
                           end
            end).
      * split.
        split; try omega; rewrite minus_diag; auto.
        intros ? []; auto.
      * destruct H; auto; destruct N; auto.
      * destruct Hn as ((H0 & H1) & H2); split.
        split; try omega; finish with H1.
        intros k (H3 & H4).
        destruct (eq_nat_dec k i).
        subst k; rewrite minus_diag in H4; destruct N; auto.
        apply H2; split.
        omega.
        finish with H4.
    Qed.

    Let bar_pe_c_fc : bar_pe 1 (f c).
    Proof.
      destruct Hx as (n & H1 & H2).
      apply iter_bar_pe with n; auto.
      apply in_bar_pe_0; auto.
    Qed.
  
    Definition floyd_period : least_div (fun n => 0 < n /\ c = f↑n c).
    Proof.
      refine (match bar_pe_inv bar_pe_c_fc with
                | exist _ n Hn => exist _ n _
              end).
              
      destruct Hn as ((H0 & H1) & H2).
      split.
      split; try omega; finish with H1.
      intros [|k] (H3 & H4); try omega.
      destruct eucl_dev with (n := n) (m := S k) as [ q [|r] H5 H6 ]; try omega.
      exists q; omega.
      
      rewrite H6 in H4.
      replace (q*n+ S r) 
        with  (S r+(q*n+0)) in H4 by omega.
      rewrite <- iter_loop_gen in H4.
      2: finish with H1.
      replace (S r + 0) 
         with ((S r-1)+1) in H4 by omega.
      rewrite iter_plus in H4.
      generalize (H2 _ (conj (Nat.lt_0_succ _) H4)).
      intro; omega.
    Defined.
    
  End compute_period.
  
  (** The output of the cycle finding algorithm is a pair i (for index) and p (for period) such that
        1/ 0 < p
        2/ f↑i x is a fixpoint of f↑p (ie f↑i x belongs to a p-loop)
        3/ f↑i x is first belonging to a loop (ie the entry point of the loop)
        4/ p divides any period 
    *)
 
  Let cycle_spec λ μ :=     0 < μ 
                         /\ f↑λ x0 = f↑(λ+μ) x0
                         /\ forall i j, i < j -> f↑i x0 = f↑j x0 -> λ <= i /\ μ div (j-i).
                
  Definition floyd_find_cycle : { λ : nat & { μ | cycle_spec λ μ } }.
  Proof.
    refine (
      match floyd_meeting_pt with exist _ c Hc => 
        match floyd_index Hc with exist _ l Hl =>
          match @floyd_period c _ with exist _ m Hm => 
            existT _ l (exist _ m _) 
          end
        end
      end); destruct Hc as (k & H1 & H2 & H3); 
            destruct Hl as (Hl1 & Hl2). 
      
    - exists k; split; auto.
      rewrite H2 at 2; finish with H3.
      
    - destruct Hm as ((Hm0 & Hm1) & Hm2).
      split; [ | split ].
      * auto.
      * apply iter_in_cycle_period; subst c; auto.
      * intros i j H4 H5; split.
        + apply Hl2.
          exists (j-i); split; try omega.
          finish with H5.
        + apply Hm2; split; try omega.
          rewrite H2, <- iter_plus, plus_comm.
          apply iter_in_cycle_period.
          exists k; rewrite <- H2 at 1.
          split; auto; finish with H3.
          split; try omega.
          exists i; finish with H5.
  Defined.

End Floyd_cycle_finding_algo.

Check floyd_find_cycle.
Print Assumptions floyd_find_cycle.
Recursive Extraction floyd_find_cycle.

