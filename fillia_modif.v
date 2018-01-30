(* author: Jean-Christophe Filliatre *)

(**
  Correctness proof of Floyd's cycle-finding algorithm, also known as     
  the "tortoise and the hare"-algorithm
  (see http://en.wikipedia.org/wiki/Floyd's_cycle-finding_algorithm)

  If $f:A\rightarrow A$ is a function over a finite set $A$, 
  then the iterations of $f$ from $x_0\in A$ will ultimately cycle. 
  The following code finds out an integer $m$ such that 
  $f^m(x_0)=f^{2m}(x_0)$ :
<<
let rec race m x y = if x = y then m else race (m+1) (f x) (f (f y))
in race 1 (f x0) (f (f x0))
>>
  The difficulty is to prove $f$'s termination.
*)

(** This code was updated modified by Dominique Larchey-Wendling
    for two reasons:
    
     a) to fill the holes (see below) 
     b) make it constructive (axiom free)
     
    Indeed, the following command at the ends of JC Filliatre
    code "Print Assumptions find_cycle." list the axioms/holes
    that are left in the code
    
    Axioms:
    
    A : Set
    eq_A_dec : forall x y : A, {x = y} + {x <> y}
    f : A -> A
    x0 : A
    
    lambda : nat
    mu : nat
    mu_positive : mu > 0
    lambda_mu : forall i j : nat, x (lambda + i) = x (lambda + i + j * mu)
            
    epsilon : (nat -> Prop) -> nat
    epsilon_spec : forall P : nat -> Prop, (exists y, P y) -> P (epsilon P)

    ex_min_P : forall P : nat -> Prop,
           (forall x : nat, {P x} + {~ P x}) ->
           (exists y, P y) -> exists y, min P y
    div : forall a : nat, a > 0 -> forall b : nat, exists k : nat, k * a >= b
    R_wf : well_founded R
 
    Some of these assumptions are "parameters" of the algorithm
    that by definition can only be filled by instanciating the
    algorithm: these are A, eq_A_dec, f and x0. Notice that
    it is not possible to detect cycles without a decidable 
    relation.
    
    Other assumptions are holes that were left empty by JC Filliatre
    for some unkown reasons. I can only speculate here that he did not
    want to bloat the code with secondary considerations that were not
    essential to understand the implentation. Or maybe he was lazy 
    (which is not necessarily a bad point ;-) 
    
    Anyway:
    - div is really trivial to show (see below) 
    - ex_min_P is also relatively easy (see below)
    - for R_wf, the only missing part is the stability of wellfoundedness 
      under lexicographic product, which is a short proof by nested
      induction
      
    Filling the epsilon/epsilon_spec holes is less easy because
    Hilbert's epsilon, especially as it is assumed here, is a non-constructive
    operator. In the Coq library, the closest corresponding operator
    is CID (Constructive Indefinite Description):
    
    ConstructiveIndefiniteDescription_on nat : 
       forall P : nat -> Prop, ex P -> sig P.
    
    From which we could derive 
    
    eps : forall P : nat -> Prop, ex P -> nat.
    eps_spec : forall P (H : ex P), P (eps P H).
    
    But this is not the same operator as epsilon because eps requires
    a proof of existence H : ex P as input while epsilon requires only P
    
    However, epsilon can be replaced with constructive_indefinite_ground_description_nat_Acc
    which I call CDD (Constructive Decidable Description) 
    
    CDD : forall P : nat -> Prop, (forall x, { P x } + { ~ P x }) -> ex P -> sig P
    
    CDD can be implemented purely constructively (axiom-free). See 
        Coq.Logic.ConstructiveEpsilon 
    or  http://www-verimag.imag.fr/~monin/Talks/talk_f91.pdf
    or my paper "Typing Total Recursive Functions in Coq" at ITP2017
    for a more detailed explanation on this subject.
    
    However, replacing epsilon with CDD comes at the price of modifying 
    the distance algorithm below (sep_x2m_xm) so that (exists i, sep_x2m_xm m i) 
    always holds and we can feed CDD with it.
    
    Basically, the static distance (number of steps the hare would
    have to perform at speed 1 to reach an static turtle) is replaced
    with the dynamic distance (how far in the future will the hare
    reach the turtle, hare moving at speed 2 and tortoise at speed 1)
    
    - The static distance does not exist if the hare preceeds the turtle
    - The dynamic distance exists as soon as there is a cycle
    
    Finally, some subtle holes are also present: lambda, mu and
    (mu_positive, lambda_mu) which express that the iteration of f 
    starting for x0 enters in a loop at some point.
    
    The problem is that lambda and mu have *informative* content:
    the assumption is NOT (exists lambda mu, such that ...) 
    And computing these values is exactly what the Floyd algorithm 
    is about. So assuming them is a kind of logical loop.
    
    Using the dynamic distance, there is no need to have
    lambda and mu because it not necessary to position the
    turtle inside or outside the cycle ...
    
    But then, this code is somewhat longer and less simple
    than the code based on bar induction ...

*)


Require Import Arith Omega Wellfounded ConstructiveEpsilon.
Open Scope nat_scope.

Definition div : forall a, a > 0 -> forall b, exists k,1 <= k /\ k*a >= b.
Proof.
  intros a Ha b.
  exists (1+b).
  destruct a; simpl.
  * omega.
  * rewrite mult_comm; simpl. 
    generalize (a*b); intro; omega.
Qed.

Section ex_min_P.

  Variables (P : nat -> Prop) (Pdec : forall x, {P x}+{~(P x)}).
  
  Lemma nat_exst_fall n : { i | i < n /\ P i } + { forall i, P i -> n <= i }.
  Proof.
    induction n as [ | n IHn ].
    * right; intros; omega.
    * destruct IHn as [ (i & H1 & H2) | H ].
      - left; exists i; split; auto; omega.
      - destruct (Pdec n).
        + left; exists n; split; auto; omega.
        + right; intros i Hi.
          destruct (eq_nat_dec n i).
          ** subst; tauto.
          ** apply H in Hi; omega.
  Qed.
  
  Definition min i := P i /\ forall j, P j -> i <= j.

  Corollary min_dec i : { min i } + { ~ min i }.
  Proof.
    destruct (Pdec i) as [ H1 | H1 ].
    * destruct (nat_exst_fall i) as [ (j & H2 & H3) | H2 ].
      - right; intros [ H4 H5 ]; apply H5 in H3; omega.
      - left; split; auto.
    * right; intros [ ]; tauto.
  Qed.

  Lemma ex_min_P : ex P -> ex min.
  Proof.
    intros (n & Hn).
    induction n as [ n IHn ] using (well_founded_induction lt_wf).
    destruct (nat_exst_fall n) as [ (i & ? & ?) | ].
    * apply IHn with i; auto.
    * exists n; split; auto. 
  Qed.

End ex_min_P.

Section tortoise_hare.

  Variables (A : Set) (eq_A_dec : forall (x y:A), {x=y}+{~x=y})
            (f : A -> A) (x0 : A).

  (** We consider the sequence $x_i = f^i(x_0)$ *)

  Fixpoint x (i:nat) { struct i } : A := 
    match i with
      | O => x0
      | S j => f (x j)
    end.
    
  Fact x_simpl i a b : x a = x b -> x (i+a) = x (i+b).
  Proof. intro; induction i as [ | i IHi ]; simpl; auto; rewrite IHi; auto. Qed.
  
  Lemma x_loop n : x n = x (2*n) -> forall j, 1 <= j -> x n = x (j*n).
  Proof.
    intros Hn.
    induction 1 as [ | j Hj IHj ]; auto.
    f_equal; omega.
    rewrite Hn.
    replace (2*n) with (n+n) by omega.
    simpl; apply x_simpl; auto.
  Qed.

  Hypothesis (Hx0 : exists τ, τ > 0 /\ x τ = x (2*τ)).

  Let sep_x2m_xm m i := x (2*(m+i)) = x (m+i).
  
  Let sep_x2m_xm_dec m : forall i, { sep_x2m_xm m i } + { ~ sep_x2m_xm m i }.
  Proof. intro; apply eq_A_dec. Qed.
  
  (* With the above definition, sep_x2m_xm is a total predicate under Hx0 *)

  Let sep_x2m_xm_total m : ex (sep_x2m_xm m).
  Proof.
    unfold sep_x2m_xm.
    destruct Hx0 as (k & H1 & H2).
    destruct (div _ H1 m) as (a & H3 & H4).
    exists (a*k-m).
    replace (m+(a*k-m)) with (a*k) by omega.
    rewrite mult_assoc.
    do 2 (rewrite <- x_loop with (1 := H2); try omega).
    auto.
  Qed.

  (* Hence the minimum always exists regardless of the position w.r.t.
     the cycle *)

  Let ex_dist_x2m_xm m : ex (min (sep_x2m_xm m)).
  Proof. apply ex_min_P; auto. Qed.

  Let epsilon m : sig (min (sep_x2m_xm m)).
  Proof.
    apply constructive_indefinite_ground_description_nat_Acc; auto.
    intro; apply min_dec; auto.
  Qed.

  Definition dist_x2m_xm m := proj1_sig (epsilon m).

  Fact dist_x2m_xm_spec m : min (sep_x2m_xm m) (dist_x2m_xm m).
  Proof. apply (proj2_sig (epsilon m)). Qed.

  (* The distance is decreasing when x m and x 2m are different *)

  Fact dist_x2m_xm_dec m : x m <> x(2*m) -> dist_x2m_xm (S m) < dist_x2m_xm m. 
  Proof.
    intros D.
    generalize (dist_x2m_xm (S m)) (dist_x2m_xm_spec (S m)) 
               (dist_x2m_xm m)     (dist_x2m_xm_spec m).
    intros dS (_ & H2) d (H3 & _).
    red in H3.
    destruct d as [ | d ].
    * contradict D; rewrite plus_comm in H3; auto.
    * replace (2*(m+S d)) with (2*(S m + d)) in H3 by omega.
      replace (m+S d) with (S m + d) in H3 by omega.
      apply H2 in H3; omega.
  Qed.

  Let R x y := dist_x2m_xm x < dist_x2m_xm y.
  Let R_wf : well_founded R.
  Proof. unfold R; apply wf_inverse_image, lt_wf. Qed. 

  Definition find_cycle_rec m : 
                forall xm x2m, 0 < m
                            -> xm = x m 
                            -> x2m = x (2*m)
                            -> { τ:nat | τ > 0 /\ x τ = x (2*τ) }.
  Proof.
    induction m as [ m IHm ] using (well_founded_induction R_wf); intros xm x2m H1 H2 H3.
    destruct (eq_A_dec xm x2m) as [ H | H ].
    exists m; rewrite <- H2, <- H3; auto.
    apply (IHm (S m)) with (xm := f xm) (x2m := f (f x2m)).
    * apply dist_x2m_xm_dec; rewrite <- H2, <- H3; auto.
    * omega.
    * rewrite H2; auto.
    * replace (2*S m) with (2+2*m) by omega.
      rewrite H3; auto.
  Defined.

  Definition find_cycle : { τ:nat | τ > 0 /\ x τ = x (2*τ) }.
  Proof.
    apply (find_cycle_rec (S O) (f x0) (f (f x0))); auto.
  Defined.

End tortoise_hare.

Check find_cycle.
Print Assumptions find_cycle.
Recursive Extraction find_cycle.

