(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Set Implicit Arguments.

Section tortoise_hare_false.

  Variables (X : Type) (eqdec : forall x y : X, { x = y } + { x <> y }) 
            (f : X -> X) (x0 : X) (H0 : False).

  Fixpoint th_false_rec x y (H : False) : nat :=
    match eqdec x y with
      | left _  => 0
      | right _ => S (th_false_rec (f x) (f (f y)) match H with end)
    end.
    
  Definition th_false := S (th_false_rec (f x0) (f (f x0)) H0).
  
End tortoise_hare_false.

Section tortoise_hare_tail_false.

  Variables (X : Type) (eqdec : forall x y : X, { x = y } + { x <> y }) 
            (f : X -> X) (x0 : X) (H0 : False).
            
  Definition th_false_tail : nat.
  Proof.
    revert H0.
    generalize 1 (f x0) (f (f x0)).
    refine (fix loop i x y H := 
      match eqdec x y with
        | left _  => i
        | right _ => loop (S i) (f x) (f (f y)) match H with end
      end).
  Defined.
  
End tortoise_hare_tail_false.

Check th_false.
Print Assumptions th_false.
Recursive Extraction th_false.

Check th_false_tail.
Print Assumptions th_false_tail.
Extraction th_false_tail.

Parameter absurd : False.

(* This one extracts to let rec loop _ = loop () of type unit -> 'a *)

Definition loop X (x : unit) : X :=
   (fix loop _ (H : False) := loop tt (match H with end)) x absurd.

(* This one is of type 'a *)

Definition universal : forall X, X := fun X => loop X tt.

Check loop.
Print Assumptions loop.
Check universal.

(* This one extracts to a general fixpoint over function types
   ie genfix phi is extensionally equal to a fixpoint of phi

   let rec genfix phi x = phi (fun y -> genfix phi y) x
*)

Section general_fixpoint.

  Variables (X Y : Type) (phi : (X -> Y) -> (X -> Y)).

  Definition genfix (x : X) : Y := 
    (fix loop x (H : False) := phi (fun y => loop y (match H with end)) x) x absurd.

End general_fixpoint.

